module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# The canonical morphism from an algebraic space to the spectrum of a ring of functions on it

Let `X` be an algebraic space over `S` and let `A` be a commutative ring with a homomorphism
`φ : A →+* Γ(X, 𝒪_X)` into its ring of global functions. Then there is a morphism
`X ⟶ Spec A` whose restriction to every étale scheme chart `V` of `X` is the morphism of
schemes `V ⟶ Spec A` attached by the `Γ`–`Spec` adjunction to `φ` followed by restriction of
functions to `V`.

The target is the spectrum of `A` as a *scheme*, read as a presheaf on the big fppf site of `S`
by its functor of points, `AlgebraicGeometry.Space.schemePoints`. It is not asked to be an
object of the site: the site is bounded by a size cutoff and `Γ(X, 𝒪_X)` is only known to be
`u`-small, so `Spec Γ(X, 𝒪_X)` need not lie below the cutoff. This is what distinguishes the
construction below from `AlgebraicGeometry.Space.affineMapOfGlobalHom`, Stacks 05Z1, which
produces a morphism of algebraic spaces into an object of the site and therefore cannot be
applied to the spectrum of the ring of global functions.

## Main definitions

* `AlgebraicGeometry.Space.schemePoints`: the functor of points of a scheme, restricted to the
  big fppf site of `S`.
* `AlgebraicGeometry.Space.specMapOfGlobalHom`: the morphism of schemes `Y ⟶ Spec A` attached
  to a ring homomorphism `A →+* Γ(Y, ⊤)`.

## Main results

* `AlgebraicGeometry.Space.isSheaf_schemePoints`: the functor of points of a scheme is a sheaf
  on the big fppf site of `S`.
* `AlgebraicGeometry.Space.exists_specMap_of_globalHom`: **the canonical morphism**
  `X ⟶ Spec A` attached to `φ : A →+* Γ(X, 𝒪_X)`, together with its value on every étale chart.

## References

* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The functor of points of a scheme on the site -/

/-- The functor of points of a scheme, restricted to the big fppf site of `S`. -/
abbrev schemePoints (T : Scheme.{u}) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (BigFppfOver.toScheme B S hS).op ⋙ yoneda.obj T

/-- **The functor of points of a scheme is a sheaf on the big fppf site of `S`.** -/
theorem isSheaf_schemePoints (T : Scheme.{u}) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (schemePoints B S hS T) := by
  have _ := BigFppfOver.toScheme_isContinuous B S hS
  have hT : Presheaf.IsSheaf Scheme.fppfTopology (yoneda.obj T) :=
    (isSheaf_iff_isSheaf_of_type _ _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.fppfTopology) (yoneda.obj T))
  exact (BigFppfOver.toScheme B S hS).op_comp_isSheaf_of_isSheaf
    (BigFppfOver.topology B S hS) Scheme.fppfTopology _ hT

/-! ### The morphism of schemes attached to a homomorphism into global functions -/

/-- The morphism of schemes `Y ⟶ Spec A` attached to a ring homomorphism
`A →+* Γ(Y, ⊤)` by the `Γ`–`Spec` adjunction. -/
def specMapOfGlobalHom {Y : Scheme.{u}} (A : Type u) [CommRing A] (ψ : A →+* Γ(Y, ⊤)) :
    Y ⟶ Spec (CommRingCat.of A) :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)

/-- Attaching a morphism to `Spec A` to a homomorphism into global functions is natural: the
composite with a morphism of schemes is attached to the pullback of functions. -/
theorem comp_specMapOfGlobalHom {Y Y' : Scheme.{u}} (A : Type u) [CommRing A]
    (g : Y' ⟶ Y) (ψ : A →+* Γ(Y, ⊤)) :
    g ≫ specMapOfGlobalHom A ψ = specMapOfGlobalHom A (g.appTop.hom.comp ψ) := by
  rw [specMapOfGlobalHom, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    specMapOfGlobalHom, ← Spec.map_comp]
  rfl

/-! ### The canonical morphism to the spectrum -/

/-- **The canonical morphism from an algebraic space to the spectrum of a ring of functions on
it.** A ring homomorphism `φ : A →+* Γ(X, 𝒪_X)` into the global functions of an algebraic space
over `S` induces a morphism `X ⟶ Spec A` of presheaves on the big fppf site of `S`, whose
restriction to every étale scheme chart `V` of `X` is the morphism of schemes attached to `φ`
followed by restriction of functions to `V`. -/
theorem exists_specMap_of_globalHom (X : AlgebraicSpaces B S hS) (A : Type u) [CommRing A]
    (φ : A →+* globalFunctions B S hS X.1) :
    ∃ p : X.1 ⟶ schemePoints B S hS (Spec (CommRingCat.of A)),
      ∀ V : SmallEtale B S hS X.1,
        yonedaEquiv (V.1.hom ≫ p) =
          specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp φ) := by
  classical
  let J := BigFppfOver.topology B S hS
  let Q := schemePoints B S hS (Spec (CommRingCat.of A))
  have hQ : Presheaf.IsSheaf J Q := isSheaf_schemePoints B S hS _
  let r (V : SmallEtale B S hS X.1) : Q.obj (op V.1.left) :=
    specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp φ)
  let k (V : SmallEtale B S hS X.1) : yoneda.obj V.1.left ⟶ Q := yonedaEquiv.symm (r V)
  have hk {V W : SmallEtale B S hS X.1} (g : V ⟶ W) :
      yoneda.map ((SmallEtale.toOver B S hS X.1).map g) ≫ k W = k V := by
    dsimp only [k]
    rw [yonedaEquiv_symm_naturality_left]
    refine congrArg yonedaEquiv.symm ?_
    change (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g) ≫
        specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X W).comp φ) =
      specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp φ)
    rw [comp_specMapOfGlobalHom]
    refine congrArg (specMapOfGlobalHom A) ?_
    ext a
    exact congrFun (globalFunctionsChartRestriction_naturality B S hS X g) (φ a)
  let D := chosenAtlasKernelPair B S hS X
  let AC := chartFromEtaleHom B S hS X D.U D.f D.etale
  let RC := chartFromEtaleHom B S hS X D.R (yoneda.map D.t ≫ D.f)
    (chart_preimage_etale B S hS X D.f D.etale D.t D.tEtale)
  let tC : RC ⟶ AC := ObjectProperty.homMk (CostructuredArrow.homMk D.t rfl)
  let sC : RC ⟶ AC := ObjectProperty.homMk (CostructuredArrow.homMk D.s D.pullback.w.symm)
  have hwk : yoneda.map D.t ≫ k AC = yoneda.map D.s ≫ k AC := (hk tC).trans (hk sC).symm
  obtain ⟨hR, hU, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS D.f D.t D.s D.pullback
    X.property D.surjective D.etale
  let RF : Sheaf J (Type u) := ⟨yoneda.obj D.R, hR⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj D.U, hU⟩
  let XF : Sheaf J (Type u) := ⟨X.1, X.property.isSheaf⟩
  let QF : Sheaf J (Type u) := ⟨Q, hQ⟩
  let tf : RF ⟶ UF := ⟨yoneda.map D.t⟩
  let sf : RF ⟶ UF := ⟨yoneda.map D.s⟩
  let ff : UF ⟶ XF := ⟨D.f⟩
  let kk : UF ⟶ QF := ⟨k AC⟩
  have hw : tf ≫ kk = sf ≫ kk := Sheaf.hom_ext hwk
  let c := Cofork.ofπ kk hw
  let p := (Classical.choice hc).desc c
  have hp : D.f ≫ p.hom = k AC := congrArg (fun z => z.hom) (show ff ≫ p = kk by
    simpa [p, c] using (Classical.choice hc).fac c WalkingParallelPair.one)
  refine ⟨p.hom, fun V => ?_⟩
  let hrep := D.etale.1
  let W := hrep.pullback V.1.hom
  let i := hrep.fst' V.1.hom
  let j := hrep.snd V.1.hom
  let hpull := hrep.isPullback' V.1.hom
  have hjEtale := D.etale.property V.1.hom (yoneda.map i) j hpull
  let WC := chartFromEtaleHom B S hS X W (yoneda.map j ≫ V.1.hom)
    (chart_preimage_etale B S hS X V.1.hom V.2 j hjEtale)
  let iC : WC ⟶ AC := ObjectProperty.homMk (CostructuredArrow.homMk i hpull.w)
  let jC : WC ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk j rfl)
  have hlocal : yoneda.map j ≫ V.1.hom ≫ p.hom = yoneda.map j ≫ k V := by
    rw [← Category.assoc, ← hpull.w, Category.assoc, hp]
    exact (hk iC).trans (hk jC).symm
  have he := congrArg yonedaEquiv hlocal
  rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality] at he
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    D.surjective.property V.1.hom (yoneda.map i) j hpull
  have _ : Etale ((BigFppfOver.toScheme B S hS).map j) := hjEtale
  have _ : Epi ((BigFppfOver.toScheme B S hS).map j) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  have hinj : Function.Injective (Q.map j.op) := fun a b hab =>
    (cancel_epi ((BigFppfOver.toScheme B S hS).map j)).1 hab
  exact (hinj he).trans (Equiv.apply_symm_apply _ _)

end AlgebraicGeometry.Space

end
