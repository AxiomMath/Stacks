module

public import StacksFrontier.RingTheory.NaiveCotangent.Henselization

/-!
# `H₁` of the naive cotangent complex along a square of ind-étale maps

For a commutative square of ring maps
```
R ──▸ R'
│      │
▼      ▼
A ──▸ A'
```
whose horizontal maps are filtered colimits of étale maps, the canonical map
`A' ⊗_A H₁(L_{A/R}) → H₁(L_{A'/R'})` is bijective.  This is the degree `1` part of the engine
`Algebra.quasiIso_baseChangeComparison_of_ind_etale` of Stacks 0D08, recorded separately because
it is the part of that engine that the comparison of the naive cotangent complex of a morphism of
algebraic spaces with the naive cotangent complexes of its charts consumes at geometric points.

## Main results

* `Algebra.bijective_h1Cotangent_map_liftBaseChange_of_ind_etale`: the bijectivity above.

## Implementation notes

The statement factors as base change along `A → A'` over the fixed ring `R`, which is
`Algebra.h1Cotangent_liftBaseChange_bijective_of_ind_etale`, followed by change of the base ring
along `R → R'` with `A'` fixed, which is bijective because `R → R'` is formally étale: the
Jacobi–Zariski sequence of `R → R' → A'` has `H₁(L_{R'/R}) = 0` and `Ω_{R'/R} = 0` at its two
ends.
-/

@[expose] public section

open Algebra CategoryTheory

universe u v

namespace Algebra

/-- **A filtered colimit of étale algebras is formally étale.** -/
theorem FormallyEtale.of_ind_etale (R : Type u) (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (hR : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R R')) :
    FormallyEtale R R' := by
  classical
  obtain ⟨J, _, _, p, hp⟩ := hR
  apply Algebra.FormallyEtale.iff_comp_bijective.mpr
  intro T _ _ I hI
  have hc (j : J) :=
    let _ : Algebra.Etale R (p.diag.obj j) := hp j
    Algebra.FormallyEtale.comp_bijective R (p.diag.obj j) I hI
  refine ⟨fun f g hfg => ?_, fun f => ?_⟩
  · suffices e : CommAlgCat.ofHom f = CommAlgCat.ofHom g from
      congrArg CommAlgCat.Hom.hom e
    refine p.isColimit.hom_ext fun j => CommAlgCat.hom_ext ((hc j).injective ?_)
    change (Ideal.Quotient.mkₐ R I).comp (f.comp (p.ι.app j).hom) =
      (Ideal.Quotient.mkₐ R I).comp (g.comp (p.ι.app j).hom)
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hfg]
  · choose l hl using fun j =>
      (Algebra.FormallyEtale.comp_bijective R (p.diag.obj j) I hI).surjective
        (f.comp (p.ι.app j).hom)
    let c : Limits.Cocone p.diag :=
      { pt := CommAlgCat.of R T
        ι.app j := CommAlgCat.ofHom (l j)
        ι.naturality i j a := by
          refine CommAlgCat.hom_ext ((hc i).injective ?_)
          change (Ideal.Quotient.mkₐ R I).comp ((l j).comp (p.diag.map a).hom) =
            (Ideal.Quotient.mkₐ R I).comp (l i)
          rw [← AlgHom.comp_assoc, hl, hl, AlgHom.comp_assoc]
          congr 1
          exact congrArg CommAlgCat.Hom.hom (p.w a) }
    refine ⟨(p.isColimit.desc c).hom, ?_⟩
    suffices e : p.isColimit.desc c ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) =
        CommAlgCat.ofHom f from congrArg CommAlgCat.Hom.hom e
    refine p.isColimit.hom_ext fun j => ?_
    change p.ι.app j ≫ p.isColimit.desc c ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) = _
    rw [← Category.assoc, p.isColimit.fac]
    exact CommAlgCat.hom_ext (hl j)

/-- **Change of base along a formally étale map is bijective on `H₁`.**  For `R → R'` formally
étale and an `R'`-algebra `A'`, the map `H₁(L_{A'/R}) → H₁(L_{A'/R'})` is bijective: the
Jacobi–Zariski sequence of `R → R' → A'` has `H₁(L_{R'/R}) = 0` and `Ω_{R'/R} = 0` at its ends. -/
theorem bijective_h1Cotangent_map_of_formallyEtale (R R' : Type u) (A' : Type v)
    [CommRing R] [CommRing R'] [CommRing A'] [Algebra R R'] [Algebra R' A'] [Algebra R A']
    [IsScalarTower R R' A'] [FormallyEtale R R'] :
    Function.Bijective (H1Cotangent.map R R' A' A') := by
  let P := Generators.self R R'
  let Q := Generators.self R' A'
  let W := Generators.self R A'
  have hd : Function.Bijective P.toExtension.cotangentComplex :=
    ⟨(Extension.subsingleton_h1Cotangent P.toExtension).mp inferInstance,
      fun y => (P.toExtension.exact_cotangentComplex_toKaehler y).mp
        (Subsingleton.elim _ _)⟩
  have hd' : LinearMap.ker (P.toExtension.cotangentComplex.baseChange A') = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((LinearEquiv.ofBijective _ hd).baseChange R' A').injective
  have hinj : Function.Injective
      (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : x.val ∈ LinearMap.ker (Q.comp P).toExtension.cotangentComplex ⊓
        LinearMap.ker (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) :=
      ⟨x.property, congrArg Subtype.val hx⟩
    rw [← Generators.Cotangent.map_ker_baseChange_cotangentComplex Q P,
      hd', Submodule.map_bot, Submodule.mem_bot] at hx'
    exact Subtype.ext hx'
  refine ⟨?_, fun y => (H1Cotangent.exact_map_δ R R' A' y).mp (Subsingleton.elim _ _)⟩
  have hi := hinj.comp (Generators.H1Cotangent.equiv W (Q.comp P)).injective
  convert hi using 1
  funext x
  change Extension.H1Cotangent.map _ x =
    Extension.H1Cotangent.map _ (Extension.H1Cotangent.map _ x)
  rw [← Extension.H1Cotangent.map_comp_apply, Extension.H1Cotangent.map_eq]

/-- **`H₁` along a square of ind-étale maps.** -/
theorem bijective_h1Cotangent_map_liftBaseChange_of_ind_etale
    (R R' : Type u) (A A' : Type v) [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
    [Algebra R R'] [Algebra R A] [Algebra A A'] [Algebra R' A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    (hR : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R R'))
    (hA : (CommAlgCat.etale.{v} A).ind.{v} (CommAlgCat.of A A')) :
    Function.Bijective ((H1Cotangent.map R R' A A').liftBaseChange A') := by
  -- `R → R'` is formally étale, being a filtered colimit of étale maps.
  have hfe : FormallyEtale R R' := FormallyEtale.of_ind_etale R R' hR
  have hbase : Function.Bijective (H1Cotangent.map R R' A' A') :=
    bijective_h1Cotangent_map_of_formallyEtale R R' A'
  have heq : (H1Cotangent.map R R' A A').liftBaseChange A' =
      H1Cotangent.map R R' A' A' ∘ₗ (H1Cotangent.map R R A A').liftBaseChange A' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    simp only [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, map_smul]
    unfold H1Cotangent.map
    rw [← Extension.H1Cotangent.map_comp_apply, Extension.H1Cotangent.map_eq]
  rw [heq]
  exact hbase.comp (h1Cotangent_liftBaseChange_bijective_of_ind_etale R A A' hA)

end Algebra

end
