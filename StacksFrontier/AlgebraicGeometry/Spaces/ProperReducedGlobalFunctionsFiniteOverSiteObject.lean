module

public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global functions of a reduced algebraic space proper over an affine object of the site

Let `U` be an object of the big fppf site of `S` whose underlying scheme is affine with
Noetherian ring of functions `R = Γ(U, 𝒪_U)`, and let `q : Z ⟶ U` be a proper morphism from a
*reduced* algebraic space over `S`.  Then the ring `Γ(Z, 𝒪_Z)` of global regular functions,
an `R`-module through pullback of functions along `q`, is a Noetherian `R`-module.

This is `AlgebraicGeometry.Space.module_finite_globalFunctions_of_isProper` of
`StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite` with the base `Spec R`
of the site replaced by an arbitrary affine object `U` of the big fppf site of an arbitrary base
scheme `S`: the proof is the same, by Chow's lemma for a proper algebraic space over an affine
object of the site
(`AlgebraicGeometry.Space.exists_properSurjective_schemeCover_of_isProper_toAffine`, Stacks 089J),
the injectivity of pullback of functions of a reduced space along a surjective scheme chart, and
the degree-zero case of Stacks 02O6 for the proper scheme of the Chow cover.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsToChart_pullbackToGlobalFunctions`: the pullback of a
  function of `U` along a morphism `q : Z ⟶ U`, read at one scheme chart of `Z`, from the base's
  `AlgebraicGeometry.Space.globalFunctionsChartEquiv_pullbackToGlobalFunctions`.
* `AlgebraicGeometry.Scheme.Hom.finite_appTop_of_isProper`: a proper morphism to an affine
  scheme with Noetherian ring of functions is finite on global sections.
* `AlgebraicGeometry.Space.isNoetherian_globalFunctions_of_isProper_of_isReduced`: the statement
  above.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A proper morphism to an affine scheme with Noetherian ring of functions is finite on
global sections.**  Composing with the isomorphism `T ≅ Spec Γ(T, ⊤)` reduces this to the
degree-zero case of Stacks 02O6, `AlgebraicGeometry.finiteGlobalSectionsOfProper`. -/
@[ega "III 4.4.2" "b) ⇒ a), special case"]
theorem Scheme.Hom.finite_appTop_of_isProper {V T : Scheme.{u}} [IsAffine T]
    [IsNoetherianRing Γ(T, ⊤)] (m : V ⟶ T) [IsProper m] : m.appTop.hom.Finite := by
  have h₀ : ((m ≫ T.isoSpec.hom).appTop).hom.Finite :=
    finiteGlobalSectionsOfProper Γ(T, ⊤) inferInstance (m ≫ T.isoSpec.hom) inferInstance
  let e : Γ(Spec Γ(T, ⊤), ⊤) ≅ Γ(T, ⊤) := Scheme.Γ.mapIso T.isoSpec.op
  have hsurj : e.inv.hom.Finite :=
    RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2
  have heq : m.appTop = e.inv ≫ (m ≫ T.isoSpec.hom).appTop := by
    rw [Scheme.Hom.comp_appTop]
    exact (e.inv_hom_id_assoc m.appTop).symm
  rw [heq]
  exact h₀.comp hsurj

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The pullback of a function of an object of the site, on all scheme charts -/

/-- **Pullback of global functions along an arbitrary scheme chart is compatible with
functions of the base**: for `q : Z ⟶ T` and a scheme chart `ρ : h_V ⟶ Z`, the value at `ρ` of
the pullback of `r` along `q` is the pullback of `r` along the underlying morphism `V ⟶ T`. -/
theorem globalFunctionsToChart_pullbackToGlobalFunctions (Z : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (q : Z ⟶ schemeSpace T) {V : BigFppfOver B S hS}
    (ρ : yoneda.obj V ⟶ Z.obj) (r : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    globalFunctionsToChart B S hS Z ρ (pullbackToGlobalFunctions B S hS Z T q r) =
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (ρ ≫ q.hom))).appTop.hom r := by
  show ((globalFunctionsChartEquiv B S hS Z).val
    (pullbackToGlobalFunctions B S hS Z T q r)).val (op (CostructuredArrow.mk ρ)) = _
  rw [globalFunctionsChartEquiv_pullbackToGlobalFunctions]
  rfl

/-! ### Reduced algebraic spaces proper over an affine object of the site -/

/-- The global functions of an algebraic space `Z` with a morphism `q : Z ⟶ T` to an object of
the site, as a module over the functions of `T` through pullback along `q`. -/
abbrev globalFunctionsModuleOfHom (Z : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (q : Z ⟶ schemeSpace T) :
    Module Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) (globalFunctions B S hS Z.obj) :=
  Module.compHom _ (pullbackToGlobalFunctions B S hS Z T q)

/-- **The global functions of a reduced algebraic space proper over an affine object of the site
with Noetherian ring of functions form a Noetherian module.**  Let `T` be an object of the big
fppf site of `S` whose scheme is affine with Noetherian ring `R` of functions, and let
`q : Z ⟶ T` be proper with `Z` reduced.  Then `Γ(Z, 𝒪_Z)` is a Noetherian (equivalently,
finite) `R`-module.

By Chow's lemma (Stacks 089J) there is a scheme `V` with a proper surjective `ρ : h_V ⟶ Z`, so
`V ⟶ T` is a proper morphism of schemes and `Γ(V, 𝒪_V)` is a finite `R`-module (Stacks 02O6 in
degree zero); pullback along `ρ` embeds `Γ(Z, 𝒪_Z)` into it `R`-linearly, `Z` being reduced. -/
theorem isNoetherian_globalFunctions_of_isProper_of_isReduced (Z : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] (q : Z ⟶ schemeSpace T)
    (hq : IsProper B S hS q.hom)
    (hred : HasEtaleLocalProperty B S hS Z.obj
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced X)) :
    @_root_.IsNoetherian (↑Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u)
      (globalFunctions B S hS Z.obj) _ _ (globalFunctionsModuleOfHom B S hS Z T q) := by
  let := globalFunctionsModuleOfHom B S hS Z T q
  obtain ⟨V, ρ, hρP, hρS⟩ := exists_properSurjective_schemeCover_of_isProper_toAffine B S hS T
    inferInstance Z.property q.hom hq
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  let m : V ⟶ T := yoneda.preimage (ρ ≫ q.hom)
  have hm : yoneda.map m = ρ ≫ q.hom := yoneda.map_preimage _
  have hcompP : IsProper B S hS (ρ ≫ q.hom) :=
    isProper_comp B S hS hVsp Z.property hT ρ q.hom hρP hq
  have hmProper : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) := by
    have hpre : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m) := by
      rw [hm]
      exact (presheaf_isProper_iff B S hS (ρ ≫ q.hom) hVsp hT
        (by rw [← hm]; exact Functor.relativelyRepresentable.map yoneda m)).mp hcompP
    change (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map m) at hpre
    have hpm := MorphismProperty.of_relative_map hpre
    exact hpm
  let := ((BigFppfOver.toScheme B S hS).map m).appTop.hom.toAlgebra
  have : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    Scheme.Hom.finite_appTop_of_isProper ((BigFppfOver.toScheme B S hS).map m)
  let φ : globalFunctions B S hS Z.obj →ₗ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    { toFun := globalFunctionsToChart B S hS Z ρ
      map_add' := map_add _
      map_smul' := fun r x => by
        show globalFunctionsToChart B S hS Z ρ (pullbackToGlobalFunctions B S hS Z T q r * x) =
          ((BigFppfOver.toScheme B S hS).map m).appTop.hom r *
            globalFunctionsToChart B S hS Z ρ x
        rw [map_mul, globalFunctionsToChart_pullbackToGlobalFunctions] }
  exact isNoetherian_of_injective φ
    (injective_globalFunctionsToChart_of_isSurjective B S hS Z hred ρ hρS)

end Space

end AlgebraicGeometry

end
