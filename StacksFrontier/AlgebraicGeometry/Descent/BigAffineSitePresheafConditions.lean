module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCartesianSheaf

/-!
# Conditions (2)–(6) of Stacks 0GZV in full, from condition (1)

Let `S` be a scheme inside a chosen big site and let `𝓕` be a *presheaf* of `𝒪_Aff`-modules on
the big affine `τ`-site `(Aff/S)_τ` which satisfies condition (1) of Stacks 0GZV: every
base-change comparison `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` is an isomorphism.  Each of conditions
(2)–(6) is a conjunction — `𝓕` is a sheaf for `τ`, *and* it is quasi-coherent on the ringed site
`((Aff/S)_τ, 𝒪_Aff)` — and this file states that conjunction.

The two conjuncts are already proved separately:
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCartesianSheaf` has the sheaf conjunct, by
flat descent of modules, and `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines`
has the quasi-coherence conjunct, for a module already given as a sheaf.  What this file adds is
that they compose: the sheaf axiom produced by the first is exactly the one the second's
hypothesis asks for, so a presheaf satisfying condition (1) satisfies the whole of each of
conditions (2)–(6).

## Main results

* `AlgebraicGeometry.bigAffineZariski_isSheaf_and_isQuasicoherentOnSite_of_cartesian` and its
  étale, smooth, syntomic and fppf counterparts: **Stacks 0GZV, condition (1) implies each of
  conditions (2)–(6) in full.**

## Implementation notes

The sections of `𝓕` live in the universe `u` of the schemes, which is the universe in which
conditions (1)–(8) of Stacks 0GZV are stated throughout this development: the quasi-coherence
conjunct is a statement about `SheafOfModules.{u}` over the structure sheaf of the ringed site,
whose sections are in `Type u` as well.  The sheaf conjunct is available there because the
descent step it rests on,
`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_covers'`, carries no condition relating
the universe of the sections to the universe of the objects of the site.

The quasi-coherence conjunct is phrased with the base-change map
`Stacks.SheafOfModules.canonicalMap` of the ringed site and the sheaf conjunct with the
base-change comparison `Stacks.PresheafOfModules.restrictionBaseChange` of the underlying
presheaf of modules.  The two are the same map, by
`Stacks.SheafOfModules.canonicalMap_eq_restrictionBaseChange`, so condition (1) is handed to
both without a comparison.

## References

* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0GZV, condition (1) implies condition (2) in full.** A presheaf of `𝒪_Aff`-modules
on `(Aff/S)_Zar` all of whose base-change comparisons `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are
isomorphisms satisfies the Zariski sheaf axiom and is quasi-coherent on the ringed site
`((Aff/S)_Zar, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (2) in full, for a presheaf of modules"]
public theorem bigAffineZariski_isSheaf_and_isQuasicoherentOnSite_of_cartesian
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : PresheafOfModules.{u}
      ((bigAffineZariskiRingedSite B S hS).O.obj ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (BigAffineZariski B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} M f)) :
    ∃ hsheaf : Presheaf.IsSheaf (BigAffineZariski.topology B S hS) M.presheaf,
      (⟨M, hsheaf⟩ : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (bigAffineZariskiRingedSite B S hS).O)).IsQuasicoherentOnSite :=
  ⟨bigAffineZariski_isSheaf_of_cartesian.{u, u} B S hS M hM,
    bigAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS _ fun _ _ f => hM f.op⟩

/-- **Stacks 0GZV, condition (1) implies condition (3) in full.** A presheaf of `𝒪_Aff`-modules
on `(Aff/S)_étale` all of whose base-change comparisons `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are
isomorphisms satisfies the étale sheaf axiom and is quasi-coherent on the ringed site
`((Aff/S)_étale, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (3) in full, for a presheaf of modules"]
public theorem bigAffineEtale_isSheaf_and_isQuasicoherentOnSite_of_cartesian
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : PresheafOfModules.{u}
      ((bigAffineEtaleRingedSite B S hS).O.obj ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (BigAffineEtale B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} M f)) :
    ∃ hsheaf : Presheaf.IsSheaf (BigAffineEtale.topology B S hS) M.presheaf,
      (⟨M, hsheaf⟩ : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (bigAffineEtaleRingedSite B S hS).O)).IsQuasicoherentOnSite :=
  ⟨bigAffineEtale_isSheaf_of_cartesian.{u, u} B S hS M hM,
    bigAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS _ fun _ _ f => hM f.op⟩

/-- **Stacks 0GZV, condition (1) implies condition (4) in full.** A presheaf of `𝒪_Aff`-modules
on `(Aff/S)_smooth` all of whose base-change comparisons `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are
isomorphisms satisfies the smooth sheaf axiom and is quasi-coherent on the ringed site
`((Aff/S)_smooth, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (4) in full, for a presheaf of modules"]
public theorem bigAffineSmooth_isSheaf_and_isQuasicoherentOnSite_of_cartesian
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (M : PresheafOfModules.{u}
      ((bigAffineSmoothRingedSite B S hS).O.obj ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (BigAffineSmooth B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} M f)) :
    ∃ hsheaf : Presheaf.IsSheaf (BigAffineSmooth.topology B S hS) M.presheaf,
      (⟨M, hsheaf⟩ : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (bigAffineSmoothRingedSite B S hS).O)).IsQuasicoherentOnSite :=
  ⟨bigAffineSmooth_isSheaf_of_cartesian.{u, u} B S hS M hM,
    bigAffineSmooth_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS _ fun _ _ f => hM f.op⟩

/-- **Stacks 0GZV, condition (1) implies condition (5) in full.** A presheaf of `𝒪_Aff`-modules
on `(Aff/S)_syntomic` all of whose base-change comparisons `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are
isomorphisms satisfies the syntomic sheaf axiom and is quasi-coherent on the ringed site
`((Aff/S)_syntomic, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (5) in full, for a presheaf of modules"]
public theorem bigAffineSyntomic_isSheaf_and_isQuasicoherentOnSite_of_cartesian
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : PresheafOfModules.{u}
      ((bigAffineSyntomicRingedSite B S hS).O.obj ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (BigAffineSyntomic B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} M f)) :
    ∃ hsheaf : Presheaf.IsSheaf (BigAffineSyntomic.topology B S hS) M.presheaf,
      (⟨M, hsheaf⟩ : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (bigAffineSyntomicRingedSite B S hS).O)).IsQuasicoherentOnSite :=
  ⟨bigAffineSyntomic_isSheaf_of_cartesian.{u, u} B S hS M hM,
    bigAffineSyntomic_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS _ fun _ _ f => hM f.op⟩

/-- **Stacks 0GZV, condition (1) implies condition (6) in full.** A presheaf of `𝒪_Aff`-modules
on `(Aff/S)_fppf` all of whose base-change comparisons `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are
isomorphisms satisfies the fppf sheaf axiom and is quasi-coherent on the ringed site
`((Aff/S)_fppf, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (6) in full, for a presheaf of modules"]
public theorem bigAffineFppf_isSheaf_and_isQuasicoherentOnSite_of_cartesian
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : PresheafOfModules.{u}
      ((bigAffineFppfRingedSite B S hS).O.obj ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (BigAffineFppf B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} M f)) :
    ∃ hsheaf : Presheaf.IsSheaf (BigAffineFppf.topology B S hS) M.presheaf,
      (⟨M, hsheaf⟩ : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (bigAffineFppfRingedSite B S hS).O)).IsQuasicoherentOnSite :=
  ⟨bigAffineFppf_isSheaf_of_cartesian.{u, u} B S hS M hM,
    bigAffineFppf_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS _ fun _ _ f => hM f.op⟩

end AlgebraicGeometry

end
