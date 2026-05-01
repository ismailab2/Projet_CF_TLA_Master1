# Projet de Conception Formelle - Algorithme d'exclusion mutuelle

## Fichiers

- `DM_Timestamp.tla` : test des timestamps.
- `DM_Timestamp.cfg` : configuration avec `N = 2`.
- `DM_Mutex.tla` : algorithme principal.
- `DM_Mutex.cfg` : configuration avec `N = 3`.
- `DM_Mutex_N4.cfg` : configuration avec `N = 4`.
- `DM_Mutex_N5.cfg` : configuration avec `N = 5`.

## Commandes

```powershell
java -XX:+UseParallelGC -jar tla2tools.jar -workers 8 -config DM_Timestamp.cfg DM_Timestamp.tla
```

```powershell
java -XX:+UseParallelGC -jar tla2tools.jar -workers 8 -config DM_Mutex.cfg DM_Mutex.tla
```

```powershell
java -XX:+UseParallelGC -jar tla2tools.jar -workers 8 -config DM_Mutex_N4.cfg DM_Mutex.tla
```

```powershell
java -XX:+UseParallelGC -jar tla2tools.jar -workers 8 -config DM_Mutex_N5.cfg DM_Mutex.tla
```

## Verification avec plusieurs valeurs de N

Pour verifier l'algorithme avec plusieurs nombres de processus, nous avons
conserve un seul fichier PlusCal/TLA, `DM_Mutex.tla`. Les fichiers de
configuration TLC permettent uniquement de changer la constante `N`.

- `DM_Mutex.cfg` : verification avec `N = 3`
- `DM_Mutex_N4.cfg` : verification avec `N = 4`
- `DM_Mutex_N5.cfg` : verification avec `N = 5`

Pour `N = 3`, TLC termine sans erreur : l'invariant `Mutex` est respecte et
aucun deadlock n'est detecte.

Pour `N = 4`, TLC trouve une violation de l'invariant `Mutex`. Dans le
contre-exemple, l'etat final contient :

```text
pc = <<"CS", "CS", "W1", "W1">>
```

Cela signifie que deux processus sont simultanement en section critique.

Pour `N = 5`, TLC trouve aussi une violation de `Mutex`. L'etat final contient :

```text
pc = <<"CS", "CS", "W1", "Request", "W1">>
```

Cela confirme que l'algorithme simplifie fonctionne pour `N = 3`, mais ne
garantit plus l'exclusion mutuelle lorsque le nombre de processus augmente.
