module

public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraConormalBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveExtComparison
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism
public import StacksFrontier.Deformation.ToposThickening.SolutionPairObstruction
public import StacksFrontier.Deformation.ToposThickening.TrivialSquareZeroSolution

/-!
# A second solution of a square-zero extension problem of ringed topoi, by a pushout

Fix the square-zero extension problem `S` of ringed topoi of [Stacks Project, Tag 08UF]:
`f : (Sh(C), O) ⟶ (Sh(B), O_B)`, a first order thickening `O_{B'} ⟶ O_B` with ideal `J`, an
`O`-module `G` and `c : f⁻¹J ⟶ G`. Let `Q` be a solution `0 ⟶ G ⟶ O' ⟶ O ⟶ 0`. The proof of
[Stacks Project, Tag 08UK] produces, from a family of generators `E` of `O` lifted to `O'` and a
map `δ : I/I² ⟶ G` out of the conormal sheaf of the presentation `f⁻¹O_B[E] ⟶ O`, a second
solution `O'_δ`. Write `φ : f⁻¹O_{B'}[E] ⟶ O'` for the algebra map sending the variables to their
lifts and `I'` for the kernel of `f⁻¹O_{B'}[E] ⟶ O`. Then `O'_δ` is the pushout of
`0 ⟶ I' ⟶ f⁻¹O_{B'}[E] ⟶ O ⟶ 0` along `ψ = φ|_{I'} + δ ∘ (I' ⟶ I/I²)`. This file constructs
`O'_δ` and proves it is a solution, and computes the lift of the generators into it on `I'`:
it is `φ|_{I'} + δ`, which is the omitted calculation of the source.

## Main definitions

* `Stacks.Sites.Conormal.IdealRestriction.ofConormal`, `.add`, `.toPushoutData`: the restriction
  datum `g ↦ h [ι g]` of a map `h` out of a conormal sheaf, sums of restriction data, and the
  input of the square-zero pushout they give.
* `...CompatibleFirstOrderThickening.liftRestriction`: `φ|_{I'}`, read in `G`.
* `...CompatibleFirstOrderThickening.pushoutSolution`: the solution `O'_δ`.
* `...CompatibleFirstOrderThickening.liftedGenerators`: the generators `E₀ ×_O O'` of `O`, which
  lift to `O'`.
* `...CompatibleFirstOrderThickening.twist`: the solution `O'_ξ` attached to a class
  `ξ ∈ Ext¹_O(NL_f, G)`, from the presentation and conormal functional of Tag 08UJ.

## Main results

* `Stacks.Sites.SqZeroPushout.pushoutMk_inl` and `Stacks.Sites.SqZeroPushout.mul_pushoutInr`: in
  the pushout `g ∈ I'` is identified with `ψ g`, and the pushout acts on its ideal through `ℬ`.
* `Stacks.Sites.Conormal.conormal_hom_ext_of_comp`: a map out of `I/I²` is determined on the
  classes of the sections of `I'`.
* `...CompatibleFirstOrderThickening.incl_pushoutSolution`: the lift of the generators into
  `O'_δ` on `I'` is `φ|_{I'} + δ`.
* `...CompatibleFirstOrderThickening.twistPairDatum_conormalMap`: the difference map of `Q` and
  `O'_ξ` is `δ`, the omitted calculation of the source.
* `...CompatibleFirstOrderThickening.pairObstruction_twist`: `o(Q, O'_ξ) = ξ`.

## Implementation notes

The source ringed topos is `AlgebraicGeometry.RingedTopos.{u, u, u}`: the square-zero pushout and
the trivial square-zero extension under it are available for a small site whose sheaves of
rings have sections in the universe of the site, as in
`StacksFrontier/Deformation/ToposThickening/TrivialSquareZeroSolution.lean`.

## References

* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

universe t u v' u' w' v₀ u₀ w₀ z₀

namespace Stacks.Sites.Conormal

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{w₀}] [J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  {A B : Sheaf J CommRingCat.{w₀}} (φ : A ⟶ B) [Presheaf.IsLocallySurjective J φ.hom]
  {G : SheafOfModules.{max w₀ u₀ v₀ z₀} (Stacks.SheafOfModules.Tensor.ringSheaf B)}

/-- **The restriction datum of a morphism out of the conormal sheaf, along a map of rings**: for
`ι : 𝒜₁ ⟶ 𝒜₂` and `h : ℐ/ℐ² ⟶ 𝒢`, `ℐ` the kernel of `φ : 𝒜₂ ⟶ ℬ`, the datum `g ↦ h [ι g]` on the
kernel `ℐ'` of `ι ≫ φ`. -/
def IdealRestriction.ofConormal {R A₁ : Sheaf J CommRingCat.{w₀}} (a : R ⟶ A) (ι : A₁ ⟶ A)
    (h : conormalSheaf.{v₀, u₀, w₀, z₀} J A B φ ⟶ G) : IdealRestriction (ι ≫ φ) G where
  app X :=
    { toFun := fun g => h.val.app X (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ X
        ⟨ι.hom.app X g, g.2⟩)
      map_zero' := by
        have e : (⟨ι.hom.app X ((0 : kernelIdeal (ι ≫ φ).hom X) : A₁.obj.obj X),
            (0 : kernelIdeal (ι ≫ φ).hom X).2⟩ : kernelIdeal φ.hom X) = 0 :=
          Subtype.ext (map_zero (ι.hom.app X).hom)
        exact (congrArg (fun y => h.val.app X (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ X y))
          e).trans ((congrArg (h.val.app X).hom (conormalClass_zero J R A B a φ X)).trans
            (map_zero (h.val.app X).hom))
      map_add' := fun g g' => by
        have e : (⟨ι.hom.app X ((g + g' : kernelIdeal (ι ≫ φ).hom X) : A₁.obj.obj X),
            (g + g').2⟩ : kernelIdeal φ.hom X) = ⟨ι.hom.app X g, g.2⟩ + ⟨ι.hom.app X g', g'.2⟩ :=
          Subtype.ext (map_add (ι.hom.app X).hom _ _)
        exact (congrArg (fun y => h.val.app X (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ X y))
          e).trans ((congrArg (h.val.app X).hom (conormalClass_add J R A B a φ X _ _)).trans
            (map_add (h.val.app X).hom _ _)) }
  app_smul X r g := by
    have e : (⟨ι.hom.app X ((r • g : kernelIdeal (ι ≫ φ).hom X) : A₁.obj.obj X),
        (r • g).2⟩ : kernelIdeal φ.hom X) = ι.hom.app X r • ⟨ι.hom.app X g, g.2⟩ :=
      Subtype.ext (map_mul (ι.hom.app X).hom _ _)
    exact (congrArg (fun y => h.val.app X (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ X y))
      e).trans ((congrArg (h.val.app X).hom (conormalClass_smul J R A B a φ X _ _)).trans
        ((h.val.app X).hom.map_smul _ _))
  app_map {X Y} f g := (congrArg (h.val.app Y).hom
    (conormalClass_map J R A B a φ f ⟨ι.hom.app X g, g.2⟩ _
      (NatTrans.naturality_apply ι.hom f (g : A₁.obj.obj X)))).trans
    (PresheafOfModules.naturality_apply h.val f _)

omit [HasWeakSheafify J CommRingCat] in
/-- `IdealRestriction.ofConormal` on sections. -/
@[simp] theorem IdealRestriction.ofConormal_app {R A₁ : Sheaf J CommRingCat.{w₀}} (a : R ⟶ A)
    (ι : A₁ ⟶ A) (h : conormalSheaf.{v₀, u₀, w₀, z₀} J A B φ ⟶ G) (X : Cᵒᵖ)
    (g : kernelIdeal (ι ≫ φ).hom X) :
    (IdealRestriction.ofConormal φ a ι h).app X g =
      h.val.app X (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ X ⟨ι.hom.app X g, g.2⟩) :=
  rfl

/-- The sum of two restriction data. -/
def IdealRestriction.add {A₁ : Sheaf J CommRingCat.{w₀}} {ψ : A₁ ⟶ B}
    (ρ σ : IdealRestriction ψ G) : IdealRestriction ψ G where
  app X := ρ.app X + σ.app X
  app_smul X r g := by
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, ρ.app_smul, σ.app_smul, smul_add]
  app_map f g := by
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, ρ.app_map, σ.app_map]
    exact (map_add (G.val.map f).hom _ _).symm

omit [HasWeakSheafify J CommRingCat] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `IdealRestriction.add` on sections. -/
@[simp] theorem IdealRestriction.add_app {A₁ : Sheaf J CommRingCat.{w₀}} {ψ : A₁ ⟶ B}
    (ρ σ : IdealRestriction ψ G) (X : Cᵒᵖ) (g : kernelIdeal ψ.hom X) :
    (IdealRestriction.add ρ σ).app X g = ρ.app X g + σ.app X g :=
  rfl

omit [HasWeakSheafify J CommRingCat] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A map out of `ℐ/ℐ²` is determined on the classes of the sections of `ℐ'`**, the kernel of
`ι ≫ φ`, when `ι` is locally surjective: a local section of `ℐ` is locally the image under `ι` of
a section, which then lies in `ℐ'`. -/
theorem conormal_hom_ext_of_comp {R A₁ : Sheaf J CommRingCat.{w₀}} (a : R ⟶ A) (ι : A₁ ⟶ A)
    [Presheaf.IsLocallySurjective J ι.hom]
    [J.HasSheafCompose (forget AddCommGrpCat.{max w₀ u₀ v₀ z₀})]
    {g₁ g₂ : conormalSheaf.{v₀, u₀, w₀, z₀} J A B φ ⟶ G}
    (h : ∀ (V : Cᵒᵖ) (p : kernelIdeal (ι ≫ φ).hom V),
      g₁.val.app V (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ V ⟨ι.hom.app V p, p.2⟩) =
        g₂.val.app V (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ V ⟨ι.hom.app V p, p.2⟩)) :
    g₁ = g₂ := by
  refine conormal_hom_ext _ G fun X x => ?_
  have hG : Presieve.IsSheaf J (G.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf _ G.isSheaf)
  refine (hG _ (Presheaf.imageSieve_mem J ι.hom (x : _))).isSeparatedFor.ext
    fun Y f ⟨p, hp⟩ => ?_
  have hp' : (p : A₁.obj.obj (Opposite.op Y)) ∈ kernelIdeal (ι ≫ φ).hom (Opposite.op Y) := by
    change φ.hom.app _ (ι.hom.app _ p) = 0
    rw [hp, NatTrans.naturality_apply, x.2, map_zero]
  have hc : ∀ g : conormalSheaf.{v₀, u₀, w₀, z₀} J A B φ ⟶ G,
      (G.val.presheaf ⋙ forget AddCommGrpCat).map f.op (g.val.app X
        (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ X x)) =
      g.val.app (Opposite.op Y) (conormalClass.{v₀, u₀, w₀, z₀} J R A B a φ (Opposite.op Y)
          ⟨ι.hom.app (Opposite.op Y) p, hp'⟩) := by
    intro g
    refine (PresheafOfModules.naturality_apply g.val f.op _).symm.trans ?_
    exact congrArg (g.val.app (Opposite.op Y)).hom
      (conormalClass_map J R A B a φ f.op x _ hp).symm
  exact (hc g₁).trans ((h (Opposite.op Y) ⟨p, hp'⟩).trans (hc g₂).symm)

end Stacks.Sites.Conormal

namespace Stacks.Sites.Conormal

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)}

/-- **A restriction datum is the input of the square-zero pushout**: the module `𝒢` is read over
`𝒜` through the presentation, on which the ideal `ℐ = Ker φ` then acts by zero. -/
def IdealRestriction.toPushoutData (ρ : IdealRestriction φ G) :
    Stacks.Sites.SqZeroPushout.PushoutData φ
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj G) where
  app X := ρ.app X
  app_smul X r g := ρ.app_smul X r g
  app_map f g := ρ.app_map f g
  smul_eq_zero X g m := by
    change (φ.hom.app X).hom (g : A.obj.obj X) • (show G.val.obj X from m) = 0
    rw [show (φ.hom.app X).hom (g : A.obj.obj X) = 0 from g.2, zero_smul]

end Stacks.Sites.Conormal

namespace Stacks.Sites.SqZeroPushout

open _root_.PresheafOfModules (sqZeroExtMk sqZeroExtFst sqZeroExtSnd sqZeroExt_ext)
open _root_.Stacks.Sheaves.Differentials (sqZeroExtSheaf sqZeroExtSheafProj sqZeroExtSheafInl)

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R B : Sheaf K CommRingCat.{u}} (π : R ⟶ B)
  (N : SheafOfModules.{u} (_root_.Stacks.Sheaves.Differentials.underlyingRingSheaf R))
  (ψ : PushoutData π N) [HasWeakSheafify K CommRingCat.{u}]

/-- **In the pushout, a section `g` of the ideal `ℐ'` is identified with `ψ g`**: the classes of
`(g, 0)` and `(0, ψ g)` agree, because their difference is the antidiagonal section of `g`. -/
theorem pushoutMk_inl (X : Cᵒᵖ) (g : kernelIdeal π.hom X) :
    (pushoutMk π N ψ).hom.app X (sqZeroExtMk (M := modules N) (g : R.obj.obj X) 0) =
      pushoutInr π N ψ X (ψ.app X g) := by
  rw [pushoutInr_eq_toSheafify]
  change ((toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))).app X).hom
      (Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) X)
        (sqZeroExtMk (M := modules N) (g : R.obj.obj X) 0)) = _
  congr 1
  refine Ideal.Quotient.eq.2 ⟨g, sqZeroExt_ext ?_ ?_⟩
  · rw [graphSection_fst]
    exact (sub_zero _).symm
  · rw [graphSection_snd]
    exact (zero_sub _).symm

section Restricted

variable {G : SheafOfModules.{u} (_root_.Stacks.Sheaves.Differentials.underlyingRingSheaf B)}
  (ψ' : PushoutData π ((SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map π)).obj G))
  [K.WEqualsLocallyBijective CommRingCat.{u}]

/-- **The pushout acts on its ideal `𝒢` through `ℬ`**, when `𝒢` is a `ℬ`-module read over `R`
through `π`: `r · [(0, n)] = [(0, p(r) n)]`, `p` the projection onto `ℬ`. Locally `r` is the
class of a section `w` of `R ⋉ 𝒢`, for which this is `pushoutMk_mul_pushoutInr`. -/
theorem mul_pushoutInr (X : Cᵒᵖ) (r : (pushoutSheaf π _ ψ').obj.obj X) (n : G.val.obj X) :
    r * pushoutInr π _ ψ' X n = pushoutInr π _ ψ' X
      ((show ↥((_root_.Stacks.Sheaves.Differentials.underlyingRingSheaf B).obj.obj X) from
        (pushoutProj π _ ψ').hom.app X r) • n) := by
  refine eq_of_locally_eq (isSheaf_forgetCommRing (pushoutSheaf π _ ψ'))
    (Presheaf.imageSieve_mem K
      (toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π _ ψ'))) r) _ _
    fun Y f hf => ?_
  obtain ⟨q, hq⟩ := hf
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hw : (pushoutMk π _ ψ').hom.app (op Y) w = ((pushoutSheaf π _ ψ').obj.map f.op).hom r :=
    hq
  have hp : (pushoutProj π _ ψ').hom.app (op Y) (((pushoutSheaf π _ ψ').obj.map f.op).hom r) =
      π.hom.app (op Y) (sqZeroExtFst w) := by
    rw [← hw]
    exact congrArg (fun t => t.app (op Y) w) (pushoutMk_comp_pushoutProj_hom π _ ψ')
  have e₂ := pushoutInr_map π _ ψ' (X := X) (Y := op Y) f.op
    ((show ↥((_root_.Stacks.Sheaves.Differentials.underlyingRingSheaf B).obj.obj X) from
        (pushoutProj π _ ψ').hom.app X r) • n)
  change ((pushoutSheaf π _ ψ').obj.map f.op).hom (r * pushoutInr π _ ψ' X n) =
    ((pushoutSheaf π _ ψ').obj.map f.op).hom (pushoutInr π _ ψ' X _)
  rw [map_mul, pushoutInr_map π _ ψ' (X := X) (Y := op Y) f.op n, e₂, ← hw]
  refine (pushoutMk_mul_pushoutInr π _ ψ' (op Y) w _).trans (congrArg _ ?_)
  change _ = G.val.map f.op _
  rw [PresheafOfModules.map_smul]
  change (show ↥((_root_.Stacks.Sheaves.Differentials.underlyingRingSheaf B).obj.obj (op Y)) from
    π.hom.app (op Y) (sqZeroExtFst w)) • (G.val.map f.op n) = _
  congr 1
  exact ((NatTrans.naturality_apply (pushoutProj π _ ψ').hom f.op r).symm.trans hp).symm

end Restricted

end Stacks.Sites.SqZeroPushout

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)

/-- The inverse image `f⁻¹O_{B'}` of the thickened base structure sheaf. -/
abbrev thickenedBaseInverseImage : Sheaf X.J CommRingCat.{u} :=
  (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension

/-- The inverse image `f⁻¹O_{B'} ⟶ f⁻¹O_B` of the base reduction. -/
abbrev baseReductionInverseImage :
    S.thickenedBaseInverseImage ⟶ (inverseImageCommRingFunctor S.f.toToposHom).obj B.O :=
  (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction

namespace CompatibleFirstOrderThickening

variable {S} (Q : S.CompatibleFirstOrderThickening) [HasWeakSheafify X.J CommRingCat.{u}]
  (E : X.Cᵒᵖ ⥤ Type u) (β : E ⟶ underlyingPresheaf X.J Q.extension)

/-- The generators `E ⟶ O' ⟶ O` of the reduced structure sheaf. -/
abbrev reducedGenerators : E ⟶ underlyingPresheaf X.J X.O :=
  β ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u})

/-- The presentation `f⁻¹O_B[E] ⟶ O` of the generators. -/
abbrev reducedPresentation :
    freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) E ⟶ X.O :=
  Stacks.SheafOfModules.presentation X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
    X.O S.f.fSharpInverseImage E (Q.reducedGenerators E β)

/-- The presentation `f⁻¹O_{B'}[E] ⟶ f⁻¹O_B[E] ⟶ O`, with the coefficients of the thickened
base. -/
abbrev thickenedPresentation : freeAlgebraSheaf X.J S.thickenedBaseInverseImage E ⟶ X.O :=
  baseChange X.J S.baseReductionInverseImage E ≫ Q.reducedPresentation E β

/-- The `f⁻¹O_{B'}`-algebra map `φ : f⁻¹O_{B'}[E] ⟶ O'` sending the variables to `β`. -/
abbrev presentationLift : freeAlgebraSheaf X.J S.thickenedBaseInverseImage E ⟶ Q.extension :=
  freeAlgebraSheafDesc X.J _ Q.extension E Q.baseMap β

/-- **The restriction of `φ` to the ideal `I'`**, read in `G`: the datum `φ|_{I'}` of the proof
of Tag 08UK. -/
def liftRestriction : IdealRestriction (Q.thickenedPresentation E β) S.G where
  app _U := AddMonoidHom.mk' (Q.liftSection (Q.reducedGenerators E β) β rfl)
    (Q.liftSection_add (Q.reducedGenerators E β) β rfl)
  app_smul _U r p := Q.liftSection_smul (Q.reducedGenerators E β) β rfl r p
  app_map g p := Q.liftSection_map (Q.reducedGenerators E β) β rfl g p

/-- `φ|_{I'}` is the preimage in `G` of `φ`. -/
theorem incl_liftRestriction (U : X.Cᵒᵖ) (p : kernelIdeal (Q.thickenedPresentation E β).hom U) :
    Q.incl ((Q.liftRestriction E β).app U p) = (Q.presentationLift E β).hom.app U p :=
  Q.incl_liftSection (Q.reducedGenerators E β) β rfl p

variable [Presheaf.IsLocallySurjective X.J (Q.reducedPresentation E β).hom]
  (δ : (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
      (Q.reducedGenerators E β)).X₁ ⟶ S.G)

/-- **The map `ψ = φ|_{I'} + δ ∘ (I' ⟶ I/I²)`** along which the presentation is pushed out in the
proof of Tag 08UK. -/
def pushoutRestriction : IdealRestriction (Q.thickenedPresentation E β) S.G :=
  IdealRestriction.add (Q.liftRestriction E β)
    (IdealRestriction.ofConormal (Q.reducedPresentation E β)
      (freeAlgebraSheafCoefficientMap X.J _ E) (baseChange X.J S.baseReductionInverseImage E) δ)

section Pushout

open Stacks.Sites.SqZeroPushout
open _root_.PresheafOfModules (sqZeroExtMk sqZeroExtFst sqZeroExtSnd sqZeroExt_ext)
open _root_.Stacks.Sheaves.Differentials (sqZeroExtSheaf sqZeroExtSheafProj sqZeroExtSheafInl)

variable [X.J.WEqualsLocallyBijective CommRingCat.{u}]

/-- `G`, read over `f⁻¹O_{B'}[E]` through the presentation. -/
abbrev pushoutModule :=
  (SheafOfModules.restrictScalars ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map
    (Q.thickenedPresentation E β))).obj S.G

/-- The datum `ψ` of the pushout. -/
abbrev pushoutDatum : PushoutData (Q.thickenedPresentation E β) (Q.pushoutModule E β) :=
  IdealRestriction.toPushoutData _ (Q.pushoutRestriction E β δ)

/-- The pushout `O'_δ` of `0 ⟶ I' ⟶ f⁻¹O_{B'}[E] ⟶ O ⟶ 0` along `ψ`. -/
abbrev pushoutRing : Sheaf X.J CommRingCat.{u} :=
  pushoutSheaf (Q.thickenedPresentation E β) (Q.pushoutModule E β) (Q.pushoutDatum E β δ)

/-- **The pushout along `ψ = φ|_{I'} + δ ∘ (I' ⟶ I/I²)` is a solution** of the extension problem,
the solution `O'_ξ` of the proof of Tag 08UK. -/
def pushoutSolution : S.CompatibleFirstOrderThickening where
  extension := Q.pushoutRing E β δ
  reduction := pushoutProj _ _ (Q.pushoutDatum E β δ)
  locallySurjective := isLocallySurjective_pushoutProj _ _ (Q.pushoutDatum E β δ)
  squareZero U := by
    refine le_antisymm ?_ bot_le
    rw [pow_two]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨n, rfl⟩ := (pushoutProj_app_eq_zero_iff _ _ (Q.pushoutDatum E β δ) U x).1 hx
    obtain ⟨m, rfl⟩ := (pushoutProj_app_eq_zero_iff _ _ (Q.pushoutDatum E β δ) U y).1 hy
    exact Ideal.mem_bot.2 (pushoutInr_mul_pushoutInr _ _ _ U n m)
  baseMap := freeAlgebraSheafCoefficientMap X.J S.thickenedBaseInverseImage E ≫
    sqZeroExtSheafInl _ (Q.pushoutModule E β) ≫ pushoutMk _ _ (Q.pushoutDatum E β δ)
  baseMap_reduction := by
    rw [Category.assoc, Category.assoc, pushoutMk_comp_pushoutProj, ← Category.assoc
      (sqZeroExtSheafInl _ _),
      Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj, Category.id_comp,
      ← Category.assoc, freeAlgebraSheafCoefficientMap_comp_baseChange, Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc]
  kernelInclusion :=
    { val :=
      { app := fun U => ModuleCat.ofHom
          (X := ((SheafOfModules.restrictScalars
            ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map
              (pushoutProj _ _ (Q.pushoutDatum E β δ)))).obj S.G).val.obj U)
          (Y := (SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj (Q.pushoutRing E β δ))).val.obj U)
          { toFun := pushoutInr _ _ (Q.pushoutDatum E β δ) U
            map_add' := pushoutInr_add _ _ (Q.pushoutDatum E β δ) U
            map_smul' := fun r n => (mul_pushoutInr _ (Q.pushoutDatum E β δ) U r n).symm }
        naturality := fun {U V} h => by
          ext n
          exact (pushoutInr_map _ _ (Q.pushoutDatum E β δ) h n).symm } }
  kernelZero U n := pushoutProj_pushoutInr _ _ (Q.pushoutDatum E β δ) U n
  kernelUniversal U a ha := by
    obtain ⟨n, hn⟩ := (pushoutProj_app_eq_zero_iff _ _ (Q.pushoutDatum E β δ) U a).1 ha
    exact ⟨n, hn, fun m hm => pushoutInr_injective _ _ (Q.pushoutDatum E β δ) U
      (hm.trans hn.symm)⟩
  baseMap_ideal U a := by
    have hx : S.baseReductionInverseImage.hom.app U (S.idealInclusion.val.app U a) = 0 :=
      S.idealZero U a
    have hb : (baseChange X.J S.baseReductionInverseImage E).hom.app U
        ((freeAlgebraSheafCoefficientMap X.J S.thickenedBaseInverseImage E).hom.app U
          (S.idealInclusion.val.app U a)) = 0 := by
      refine (congrArg (fun t => t.hom.app U (S.idealInclusion.val.app U a))
        (freeAlgebraSheafCoefficientMap_comp_baseChange X.J S.baseReductionInverseImage E)).trans ?_
      change (freeAlgebraSheafCoefficientMap X.J _ E).hom.app U
        (S.baseReductionInverseImage.hom.app U (S.idealInclusion.val.app U a)) = 0
      rw [hx, map_zero]
    have hc : (Q.thickenedPresentation E β).hom.app U
        ((freeAlgebraSheafCoefficientMap X.J S.thickenedBaseInverseImage E).hom.app U
          (S.idealInclusion.val.app U a)) = 0 := by
      change (Q.reducedPresentation E β).hom.app U ((baseChange X.J S.baseReductionInverseImage
        E).hom.app U _) = 0
      rw [hb, map_zero]
    let g : kernelIdeal (Q.thickenedPresentation E β).hom U := ⟨_, hc⟩
    change (pushoutMk _ _ (Q.pushoutDatum E β δ)).hom.app U
      (sqZeroExtMk (M := Q.pushoutModule E β |>.val)
        (g : (freeAlgebraSheaf X.J S.thickenedBaseInverseImage E).obj.obj U) 0) =
        pushoutInr _ _ (Q.pushoutDatum E β δ) U (S.c.val.app U a)
    rw [pushoutMk_inl _ _ (Q.pushoutDatum E β δ) U g]
    congr 1
    have h₁ : (Q.liftRestriction E β).app U g = S.c.val.app U a := by
      refine Q.incl_injective ((Q.incl_liftRestriction E β U g).trans ?_)
      exact (congrArg (fun t => t.hom.app U (S.idealInclusion.val.app U a))
        (freeAlgebraSheafCoefficientMap_comp_desc X.J S.thickenedBaseInverseImage Q.extension E
          Q.baseMap β)).trans (Q.baseMap_ideal U a)
    change (Q.liftRestriction E β).app U g + _ = _
    rw [h₁]
    refine (congrArg (S.c.val.app U a + ·) ?_).trans (add_zero _)
    change (δ.val.app U).hom (conormalClass X.J _ _ X.O (freeAlgebraSheafCoefficientMap X.J _ E)
      (Q.reducedPresentation E β) U ⟨(baseChange X.J S.baseReductionInverseImage E).hom.app U g,
        g.2⟩) = 0
    refine (congrArg (δ.val.app U).hom ?_).trans (map_zero (δ.val.app U).hom)
    have h0 : (⟨(baseChange X.J S.baseReductionInverseImage E).hom.app U g, g.2⟩ :
        kernelIdeal (Q.reducedPresentation E β).hom U) = 0 :=
      Subtype.ext hb
    rw [h0]
    exact conormalClass_zero X.J _ _ _ _ _ U

/-- The generators `E ⟶ O'_δ`: the variables, sent through `f⁻¹O_{B'}[E] ⟶ O'_δ`. -/
abbrev pushoutGenerators : E ⟶ underlyingPresheaf X.J (Q.pushoutSolution E β δ).extension :=
  freeAlgebraSheafVariable X.J S.thickenedBaseInverseImage E ≫ Functor.whiskerRight
    ((sheafToPresheaf X.J CommRingCat.{u}).map
      (sqZeroExtSheafInl _ (Q.pushoutModule E β) ≫ pushoutMk _ _ (Q.pushoutDatum E β δ)))
    (forget CommRingCat.{u})

/-- The lift `f⁻¹O_{B'}[E] ⟶ O'_δ` of the generators is `p ↦ [(p, 0)]`. -/
theorem presentationLift_pushoutSolution :
    (Q.pushoutSolution E β δ).presentationLift E (Q.pushoutGenerators E β δ) =
      sqZeroExtSheafInl _ (Q.pushoutModule E β) ≫ pushoutMk _ _ (Q.pushoutDatum E β δ) := by
  refine freeAlgebraSheaf_hom_ext X.J _ _ E ?_ ?_
  · rw [presentationLift, freeAlgebraSheafCoefficientMap_comp_desc]
    rfl
  · rw [presentationLift, freeAlgebraSheafVariable_comp_desc]
    rfl

/-- The generators of `O'_δ` and of `Q` have the same image in `O`. -/
theorem reducedGenerators_pushoutSolution :
    (Q.pushoutSolution E β δ).reducedGenerators E (Q.pushoutGenerators E β δ) =
      Q.reducedGenerators E β := by
  have h : sqZeroExtSheafInl _ (Q.pushoutModule E β) ≫ pushoutMk _ _ (Q.pushoutDatum E β δ) ≫
      pushoutProj _ _ (Q.pushoutDatum E β δ) = Q.thickenedPresentation E β := by
    rw [pushoutMk_comp_pushoutProj, ← Category.assoc,
      Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj, Category.id_comp]
  refine Eq.trans (?_ : _ = freeAlgebraSheafVariable X.J S.thickenedBaseInverseImage E ≫
    Functor.whiskerRight ((sheafToPresheaf X.J CommRingCat.{u}).map
      (Q.thickenedPresentation E β)) (forget CommRingCat.{u})) ?_
  · rw [← h, Functor.map_comp, Functor.map_comp, Functor.whiskerRight_comp,
      Functor.whiskerRight_comp, ← Category.assoc]
    rfl
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_baseChange]
    exact freeAlgebraSheafVariable_comp_desc X.J _ X.O E _ _

/-- **The lift into `O'_δ` on the ideal `I'`**: for `p` in `I' = Ker(f⁻¹O_{B'}[E] ⟶ O)` the lift
of the generators of `O'_δ` sends `p` to the section `φ|_{I'}(p) + δ[p]` of `G`, where `[p]` is
the class in `I/I²` of the image of `p` in `f⁻¹O_B[E]`. -/
theorem incl_pushoutSolution (U : X.Cᵒᵖ) (p : kernelIdeal (Q.thickenedPresentation E β).hom U) :
    (Q.pushoutSolution E β δ).incl ((Q.liftRestriction E β).app U p +
        δ.val.app U (conormalClass X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) _
          X.O (freeAlgebraSheafCoefficientMap X.J _ E) (Q.reducedPresentation E β) U
          ⟨(baseChange X.J S.baseReductionInverseImage E).hom.app U p, p.2⟩)) =
      ((Q.pushoutSolution E β δ).presentationLift E (Q.pushoutGenerators E β δ)).hom.app U p := by
  rw [presentationLift_pushoutSolution]
  exact (congrArg (pushoutInr _ _ (Q.pushoutDatum E β δ) U) rfl).trans
    (pushoutMk_inl _ _ (Q.pushoutDatum E β δ) U p).symm

end Pushout

/-! ### Generators lifted to a solution -/

section Refinement

variable {E₀ : X.Cᵒᵖ ⥤ Type u} (α : E₀ ⟶ underlyingPresheaf X.J X.O)

/-- The reduction of `Q`, on underlying presheaves of sets. -/
abbrev reductionSet : underlyingPresheaf X.J Q.extension ⟶ underlyingPresheaf X.J X.O :=
  Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u})

/-- **The generators `E₀ ×_O O'`**: a family of generators of `O` refined so that every generator
comes with a lift to the solution `Q`, as in the proof of Tag 08UK. -/
abbrev liftedGenerators : X.Cᵒᵖ ⥤ Type u := Limits.pullback α Q.reductionSet

/-- The lifts of the refined generators to `Q`. -/
abbrev liftedGeneratorsLift : Q.liftedGenerators α ⟶ underlyingPresheaf X.J Q.extension :=
  Limits.pullback.snd α Q.reductionSet

/-- The refined generators map to the given ones. -/
abbrev liftedGeneratorsFst : Q.liftedGenerators α ⟶ E₀ := Limits.pullback.fst α Q.reductionSet

omit [HasWeakSheafify X.J CommRingCat] in
/-- The refined generators have the same image in `O` as the given ones. -/
theorem reducedGenerators_liftedGenerators :
    Q.reducedGenerators (Q.liftedGenerators α) (Q.liftedGeneratorsLift α) =
      Q.liftedGeneratorsFst α ≫ α :=
  Limits.pullback.condition.symm

/-- The reduction of a solution is locally surjective on underlying presheaves of sets. -/
instance isLocallySurjective_reductionSet :
    Presheaf.IsLocallySurjective X.J Q.reductionSet :=
  (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q.reduction.hom).1 Q.locallySurjective

/-- If the given generators are locally surjective onto `O`, so are the refined ones, and then
`f⁻¹O_B[E₀ ×_O O'] ⟶ O` is locally surjective. -/
theorem isLocallySurjective_reducedPresentation_liftedGenerators
    [Presheaf.IsLocallySurjective X.J α] :
    Presheaf.IsLocallySurjective X.J
      (Q.reducedPresentation (Q.liftedGenerators α) (Q.liftedGeneratorsLift α)).hom := by
  have : Presheaf.IsLocallySurjective X.J (Q.liftedGeneratorsFst α) :=
    Presheaf.isLocallySurjective_pullback_fst X.J α Q.reductionSet
  have : Presheaf.IsLocallySurjective X.J
      (Q.reducedGenerators (Q.liftedGenerators α) (Q.liftedGeneratorsLift α)) := by
    rw [reducedGenerators_liftedGenerators]
    infer_instance
  exact (Presheaf.isLocallySurjective_iff_whisker_forget X.J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac X.J
      (freeAlgebraSheafVariable_comp_desc X.J _ X.O _ _ _))

end Refinement

/-! ### The second solution attached to a class -/

section Twist

variable [X.J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

omit [X.J.WEqualsLocallyBijective CommRingCat] in
/-- The family of generators, its map to `O`, and the conormal functional that
`Stacks.SheafOfModules.exists_locallySurjective_presentation_conormalExtClass` (Tag 08UJ)
attaches to a class
`ξ ∈ Ext¹_O(NL_f, G)`. -/
theorem exists_twistDatum (ξ : S.f.naiveCotangentExt S.G 1) :
    ∃ (E₀ : Sheaf X.J (Type u)) (α : E₀.obj ⟶ underlyingPresheaf X.J X.O)
      (_ : Presheaf.IsLocallySurjective X.J α)
      (hsurj : Presheaf.IsLocallySurjective X.J (Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
          E₀.obj α).hom),
      letI := hsurj
      ∃ f : (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
            E₀.obj α).X₁ ⟶ S.G,
        DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
            X.J _ X.O S.f.fSharpInverseImage E₀.obj α) ≫ ξ =
          Stacks.SheafOfModules.presentationConormalExtClass.{u, u, u, t} X.J _ X.O
            S.f.fSharpInverseImage E₀.obj α S.G f :=
  Stacks.SheafOfModules.exists_locallySurjective_presentation_conormalExtClass.{u, u, u, t} X.J _
    X.O S.f.fSharpInverseImage S.G ξ

variable (ξ : S.f.naiveCotangentExt S.G 1)

/-- The family of generators of `O` that Tag 08UJ attaches to `ξ`. -/
abbrev twistGenerators : X.Cᵒᵖ ⥤ Type u := (exists_twistDatum (S := S) ξ).choose.obj

/-- Its map to `O`. -/
abbrev twistGeneratorsMap : twistGenerators (S := S) ξ ⟶ underlyingPresheaf X.J X.O :=
  (exists_twistDatum (S := S) ξ).choose_spec.choose

/-- The generators of Tag 08UJ are locally surjective onto `O`. -/
instance isLocallySurjective_twistGeneratorsMap :
    Presheaf.IsLocallySurjective X.J (twistGeneratorsMap (S := S) ξ) :=
  (exists_twistDatum (S := S) ξ).choose_spec.choose_spec.choose

/-- The generators of Tag 08UJ present `O`. -/
instance isLocallySurjective_twistPresentation :
    Presheaf.IsLocallySurjective X.J (Stacks.SheafOfModules.presentation X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
        (twistGenerators (S := S) ξ) (twistGeneratorsMap (S := S) ξ)).hom :=
  (exists_twistDatum (S := S) ξ).choose_spec.choose_spec.choose_spec.choose

/-- The conormal functional that Tag 08UJ attaches to `ξ`. -/
def twistFunctional : (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
      (twistGenerators (S := S) ξ) (twistGeneratorsMap (S := S) ξ)).X₁ ⟶ S.G :=
  (exists_twistDatum (S := S) ξ).choose_spec.choose_spec.choose_spec.choose_spec.choose

omit [X.J.WEqualsLocallyBijective CommRingCat] in
/-- `ξ`, read on the presentation of Tag 08UJ, is the class of `twistFunctional ξ`. -/
theorem comparison_comp_eq_twistFunctional :
    DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
        X.J _ X.O S.f.fSharpInverseImage (twistGenerators (S := S) ξ)
          (twistGeneratorsMap (S := S) ξ)) ≫ ξ =
      Stacks.SheafOfModules.presentationConormalExtClass.{u, u, u, t} X.J _ X.O
        S.f.fSharpInverseImage _ _ S.G (twistFunctional (S := S) ξ) :=
  (exists_twistDatum (S := S) ξ).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

/-- The refined generators of Tag 08UJ present `O`. -/
instance isLocallySurjective_reducedPresentation_twist :
    Presheaf.IsLocallySurjective X.J (Q.reducedPresentation
      (Q.liftedGenerators (twistGeneratorsMap (S := S) ξ))
        (Q.liftedGeneratorsLift (twistGeneratorsMap (S := S) ξ))).hom :=
  Q.isLocallySurjective_reducedPresentation_liftedGenerators _

/-- The conormal functional of `ξ` on the refined generators `E₀ ×_O O'`. -/
def twistLiftedFunctional : (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
      (Q.liftedGenerators (twistGeneratorsMap (S := S) ξ))
      (Q.reducedGenerators _ (Q.liftedGeneratorsLift (twistGeneratorsMap (S := S) ξ)))).X₁ ⟶
    S.G :=
  Stacks.SheafOfModules.presentationConormalMap.{u, u, u, u} X.J _ _ _
      (Q.liftedGeneratorsFst (twistGeneratorsMap (S := S) ξ)) X.O S.f.fSharpInverseImage _ _
      (Q.reducedGenerators_liftedGenerators _).symm ≫
    twistFunctional (S := S) ξ

/-- **The solution `O'_ξ` of the proof of Tag 08UK**: the pushout of `f⁻¹O_{B'}[E₀ ×_O O']` along
`φ|_{I'} + δ`, for the presentation `E₀` and the conormal functional `δ` that Tag 08UJ attaches to
`ξ`. -/
def twist : S.CompatibleFirstOrderThickening :=
  Q.pushoutSolution _ _ (Q.twistLiftedFunctional ξ)

/-- The pair datum of `Q` and `O'_ξ`: the refined generators `E₀ ×_O O'` with their lifts to `Q`
and their images in `O'_ξ`. -/
def twistPairDatum : PairDatum Q (Q.twist ξ) where
  E := Q.liftedGenerators (twistGeneratorsMap (S := S) ξ)
  α := Q.reducedGenerators _ (Q.liftedGeneratorsLift (twistGeneratorsMap (S := S) ξ))
  β₁ := Q.liftedGeneratorsLift (twistGeneratorsMap (S := S) ξ)
  β₂ := Q.pushoutGenerators _ _ (Q.twistLiftedFunctional ξ)
  comm₁ := rfl
  comm₂ := Q.reducedGenerators_pushoutSolution _ _ (Q.twistLiftedFunctional ξ)
  isLocallySurjective := Q.isLocallySurjective_reducedPresentation_liftedGenerators _

/-- **The omitted calculation of Tag 08UK**: the difference map `D̄` of `Q` and `O'_ξ` on the
refined generators is the conormal functional `δ` the pushout was formed with. -/
theorem twistPairDatum_conormalMap :
    (Q.twistPairDatum ξ).conormalMap = Q.twistLiftedFunctional ξ := by
  refine conormal_hom_ext_of_comp (Q.twistPairDatum ξ).presentation
    (freeAlgebraSheafCoefficientMap X.J _ (Q.twistPairDatum ξ).E)
    (baseChange X.J S.baseReductionInverseImage (Q.twistPairDatum ξ).E) fun V p => ?_
  refine ((Q.twistPairDatum ξ).conormalMap_conormalClass p
    ((Q.liftRestriction _ _).app V p)
    ((Q.liftRestriction _ _).app V p + (Q.twistLiftedFunctional ξ).val.app V _)
    (Q.incl_liftRestriction _ _ V p)
    (Q.incl_pushoutSolution _ _ (Q.twistLiftedFunctional ξ) V p)).trans (add_sub_cancel_left _ _)

/-- **Every class is the obstruction of a pair of solutions** ([Stacks Project, Tag 08UK], the
realization step): for a solution `Q` and `ξ ∈ Ext¹_O(NL_f, G)`, the solution `O'_ξ` satisfies
`o(Q, O'_ξ) = ξ`. -/
theorem pairObstruction_twist : pairObstruction Q (Q.twist ξ) = ξ := by
  rw [← (Q.twistPairDatum ξ).obstruction_eq_pairObstruction, ← cancel_epi (DerivedCategory.Q.map
    (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u} X.J _ X.O
      S.f.fSharpInverseImage (Q.twistPairDatum ξ).E (Q.twistPairDatum ξ).generatorsMap)),
    PairDatum.Q_map_comparison_comp_obstruction, PairDatum.extClass,
    twistPairDatum_conormalMap, twistLiftedFunctional]
  refine (Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_comp_conormalExtClass
    X.J _ X.O S.f.fSharpInverseImage _ _ (Q.liftedGeneratorsFst (twistGeneratorsMap (S := S) ξ))
    _ _ (Q.reducedGenerators_liftedGenerators _).symm S.G (twistFunctional (S := S) ξ)).symm.trans
      ?_
  rw [← comparison_comp_eq_twistFunctional, ← Category.assoc, ← Functor.map_comp,
    Stacks.SheafOfModules.naiveCotangentComplexComparison_naturality]
  rfl

end Twist

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
