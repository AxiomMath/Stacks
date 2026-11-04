module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteFlatAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteFlatAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiLocalTypesComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Flatness is preserved and reflected by `𝓕 ↦ 𝓕^a`, site by site

Let `S` be a scheme and `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.  Descent, Lemma 05VG
says that for a quasi-coherent `𝒪_S`-module `𝓕` and its associated module `𝓕^a` of Descent,
Proposition 03DX,

    `𝓕` is flat  ⇔  `𝓕^a` is flat as an `𝒪`-module,

both on the big site `(Sch/S)_τ` and on the small site `S_τ`.  Flatness is that of Modules on
Sites, Definition 03ER (3): `𝓖 ↦ 𝓖 ⊗_𝒪 𝓕` is an exact endofunctor of `Mod(𝒪)`, which is
`Stacks.SheafOfModules.IsFlat`.  It is read on both sides with the site's own structure sheaf:
on the left for `𝓕` on the ringed site `S.zariskiRingedSite` of the opens of `S` with `𝒪_S`, on
the right for `𝓕^a` on the big or small site with its structure sheaf `𝒪`.

This file states the flat clause of 05VG once for each of the ten sites, at the
associated-module functor of 03DX on that site and for the concrete topology; the declarations
lie in the namespace `AlgebraicGeometry.Cells05VG`:

| site               | declaration                                         |
|--------------------|-----------------------------------------------------|
| `(Sch/S)_Zar`      | `isFlat_iff_baseAssociatedModule_zariski`           |
| `(Sch/S)_étale`    | `isFlat_iff_baseAssociatedModule_etale`             |
| `(Sch/S)_smooth`   | `isFlat_iff_baseAssociatedModule_smooth`            |
| `(Sch/S)_syntomic` | `isFlat_iff_baseAssociatedModule_syntomic`          |
| `(Sch/S)_fppf`     | `isFlat_iff_baseAssociatedModule_fppf`              |
| `S_Zar`            | `isFlat_iff_smallZariskiAssociatedModule`           |
| `S_étale`          | `isFlat_iff_smallEtaleAssociatedModule`             |
| `S_smooth`         | `isFlat_iff_smallFlatSiteAssociatedModule_smooth`   |
| `S_syntomic`       | `isFlat_iff_smallFlatSiteAssociatedModule_syntomic` |
| `S_fppf`           | `isFlat_iff_smallFlatSiteAssociatedModule_fppf`     |

The functors are `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` on the big sites,
`AlgebraicGeometry.SmallZariski.associatedModule` on `S_Zar`,
`AlgebraicGeometry.SmallEtale.associatedModule` on `S_étale`, and
`AlgebraicGeometry.SmallFlatSite.associatedModule` on the small smooth, syntomic and fppf sites.

## Main results

The ten declarations of the table.  The only data of each are the scheme `S`, a big site
containing it, and `𝓕` with its quasi-coherence; no comparison of topoi is a hypothesis.

## Implementation notes

The proofs are the general flatness comparisons of the library at the given topology:
`AlgebraicGeometry.BigFppfOver.isFlat_baseAssociatedModule_iff` for the big sites,
`AlgebraicGeometry.SmallFlatSite.isFlat_associatedModule_iff` for the small smooth, syntomic and
fppf sites, and on `S_Zar` and `S_étale` the comparisons
`AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule` and
`AlgebraicGeometry.SmallEtale.isFlat_associatedModule_iff`, which hold for every `𝒪_S`-module.
On `S_Zar` the comparison `S_Zar → (S, 𝒪_S)` is an equivalence of ringed topoi and flatness
transfers by Modules on Sites, Lemma 05VD in both directions; on `S_étale` the pullback of
modules along `S_étale → S_Zar` is exact and detects zero (Stacks 08H8), hence preserves and
reflects monomorphisms and therefore reflects flatness.  On the big sites and on the small flat
sites quasi-coherence is used: the sections of `𝓕^a` over `T → S` are those of the pullback of
`𝓕` to `T`, and flatness is checked by the equational criterion of Stacks 08FC.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Cells05VG

/-! ### The big sites `(Sch/S)_τ` -/

/-- **Descent, Lemma 05VG, flat, on the big site `(Sch/S)_Zar`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `(Sch/S)_Zar`. -/
@[stacks 05VG "flat, big site (Sch/S)_Zar"]
theorem isFlat_iff_baseAssociatedModule_zariski (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (BigFppfOver.baseRingedSite B S hS .zariski).O)
        ((BigFppfOver.baseAssociatedModule B S hS .zariski).obj 𝓕) :=
  BigFppfOver.isFlat_baseAssociatedModule_iff B S hS .zariski 𝓕

/-- **Descent, Lemma 05VG, flat, on the big site `(Sch/S)_étale`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `(Sch/S)_étale`. -/
@[stacks 05VG "flat, big site (Sch/S)_étale"]
theorem isFlat_iff_baseAssociatedModule_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (BigFppfOver.baseRingedSite B S hS .etale).O)
        ((BigFppfOver.baseAssociatedModule B S hS .etale).obj 𝓕) :=
  BigFppfOver.isFlat_baseAssociatedModule_iff B S hS .etale 𝓕

/-- **Descent, Lemma 05VG, flat, on the big site `(Sch/S)_smooth`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `(Sch/S)_smooth`. -/
@[stacks 05VG "flat, big site (Sch/S)_smooth"]
theorem isFlat_iff_baseAssociatedModule_smooth (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (BigFppfOver.baseRingedSite B S hS .smooth).O)
        ((BigFppfOver.baseAssociatedModule B S hS .smooth).obj 𝓕) :=
  BigFppfOver.isFlat_baseAssociatedModule_iff B S hS .smooth 𝓕

/-- **Descent, Lemma 05VG, flat, on the big site `(Sch/S)_syntomic`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on
`(Sch/S)_syntomic`. -/
@[stacks 05VG "flat, big site (Sch/S)_syntomic"]
theorem isFlat_iff_baseAssociatedModule_syntomic (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (BigFppfOver.baseRingedSite B S hS .syntomic).O)
        ((BigFppfOver.baseAssociatedModule B S hS .syntomic).obj 𝓕) :=
  BigFppfOver.isFlat_baseAssociatedModule_iff B S hS .syntomic 𝓕

/-- **Descent, Lemma 05VG, flat, on the big site `(Sch/S)_fppf`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `(Sch/S)_fppf`. -/
@[stacks 05VG "flat, big site (Sch/S)_fppf"]
theorem isFlat_iff_baseAssociatedModule_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (BigFppfOver.baseRingedSite B S hS .fppf).O)
        ((BigFppfOver.baseAssociatedModule B S hS .fppf).obj 𝓕) :=
  BigFppfOver.isFlat_baseAssociatedModule_iff B S hS .fppf 𝓕

/-! ### The small sites `S_τ` -/

/-- **Descent, Lemma 05VG, flat, on the small site `S_Zar`.**  A quasi-coherent `𝒪_S`-module `𝓕`
is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `S_Zar`.

Quasi-coherence is the source's hypothesis and is not used:
`AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule` holds for every `𝒪_S`-module. -/
@[stacks 05VG "flat, small site S_Zar"]
theorem isFlat_iff_smallZariskiAssociatedModule (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (smallZariskiRingedSite B S hS).O)
        ((SmallZariski.associatedModule B S hS).obj 𝓕) :=
  SmallZariski.isFlat_iff_associatedModule B S hS 𝓕

/-- **Descent, Lemma 05VG, flat, on the small site `S_étale`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `S_étale`.

Quasi-coherence is the source's hypothesis and is not used:
`AlgebraicGeometry.SmallEtale.isFlat_associatedModule_iff` holds for every `𝒪_S`-module. -/
@[stacks 05VG "flat, small site S_étale"]
theorem isFlat_iff_smallEtaleAssociatedModule (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (smallEtaleRingedSite B S hS).O)
        ((SmallEtale.associatedModule B S hS).obj 𝓕) :=
  SmallEtale.isFlat_associatedModule_iff B S hS 𝓕

/-- **Descent, Lemma 05VG, flat, on the small site `S_smooth`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `S_smooth`. -/
@[stacks 05VG "flat, small site S_smooth"]
theorem isFlat_iff_smallFlatSiteAssociatedModule_smooth (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (SmallFlatSite.ringedSite B S hS .smooth).O)
        ((SmallFlatSite.associatedModule B S hS .smooth).obj 𝓕) :=
  SmallFlatSite.isFlat_associatedModule_iff B S hS .smooth 𝓕

/-- **Descent, Lemma 05VG, flat, on the small site `S_syntomic`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `S_syntomic`. -/
@[stacks 05VG "flat, small site S_syntomic"]
theorem isFlat_iff_smallFlatSiteAssociatedModule_syntomic (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (SmallFlatSite.ringedSite B S hS .syntomic).O)
        ((SmallFlatSite.associatedModule B S hS .syntomic).obj 𝓕) :=
  SmallFlatSite.isFlat_associatedModule_iff B S hS .syntomic 𝓕

/-- **Descent, Lemma 05VG, flat, on the small site `S_fppf`.**  A quasi-coherent `𝒪_S`-module
`𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `S_fppf`. -/
@[stacks 05VG "flat, small site S_fppf"]
theorem isFlat_iff_smallFlatSiteAssociatedModule_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (SmallFlatSite.ringedSite B S hS .fppf).O)
        ((SmallFlatSite.associatedModule B S hS .fppf).obj 𝓕) :=
  SmallFlatSite.isFlat_associatedModule_iff B S hS .fppf 𝓕

end AlgebraicGeometry.Cells05VG

end
