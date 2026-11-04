module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesCmpAssembly
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSpecStructureHomogeneous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationCoproductSections

/-!
# The sheaf-level identity of [Stacks, Tag 0897], proved

`Stacks.Cohomology.FormalFunctions.ReesSmulCompatible` is the one identity of morphisms of
sheaves that the `B`-linearity of [Stacks, Tag 0897]'s comparison reduces to: for `b`
homogeneous of degree `k` in `B = ⨁ₙ Iⁿ`, the direct image along `π : X' ⟶ X` of multiplication
by `b` on `F'` is, through `ε : ∐ₙ Mₙ ≅ π_* F'`, the degreewise action
`Stacks.Cohomology.FormalFunctions.actHom` of `b` on `∐ₙ Mₙ`. **This file proves it** at the
identification `Stacks.Cohomology.FormalFunctions.reesCoprodPushforwardIso`.

## The shape of the proof

`ε` is a threefold composite: the coproduct comparison
`SheafOfModules.GradedModule.coprodIsoUngradedSheaf` of the graded module, then the defining
isomorphism `Stacks.Cohomology.FormalFunctions.reesBaseChangeModuleIso` of `F'` — an isomorphism
of `⨁ₙ ℐⁿ`-modules, not merely of `𝒪_X`-modules — then the identification of [Stacks, Tag 01SB]'s
functor with the direct image. Correspondingly the identity splits into three:

* the identification is an equality of *objects*, so the direct image of a morphism and the
  `⨁ₙ ℐⁿ`-module morphism it comes from differ by that `eqToHom` on either side. That is
  `Stacks.Cohomology.FormalFunctions.restrictScalars_relativeSpecQcohEquivalence_functor_map`,
  which comes from the equality of *functors*
  `Stacks.Cohomology.FormalFunctions.restrictScalars_relativeSpecQcohEquivalence_functor`
  behind the object equality already recorded in
  `restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj`;
* multiplication by `b` is then multiplication by a section of `⨁ₙ ℐⁿ`, so the `⨁ₙ ℐⁿ`-linear
  `reesBaseChangeModuleIso` commutes with it, and on the coproduct side
  `SheafOfModules.GradedModule.coprodIsoUngradedSheaf_hom_sigma_ι_smul` says that
  multiplication by a homogeneous section is degreewise. That is the section-level computation
  `rees_smul_key`;
* which section of `⨁ₙ ℐⁿ` it is, is
  `Stacks.Cohomology.FormalFunctions.specAlgebraRingHom_reesSpecStructure_reesGrading`: the
  degree-`k` inclusion of `Stacks.Cohomology.FormalFunctions.gradedReesSection`. Here it is
  needed over every open, which is
  `Stacks.Cohomology.FormalFunctions.pushforwardRingIso_inv_app_ungradedIncl`.

## Main results

* `Stacks.Cohomology.FormalFunctions.restrictScalars_relativeSpecQcohEquivalence_functor` and
  `Stacks.Cohomology.FormalFunctions.restrictScalars_relativeSpecQcohEquivalence_functor_map`:
  [Stacks, Tag 01SB]'s functor, followed by restriction of scalars, **is** the direct image —
  as functors, and so on morphisms.
* `Stacks.Cohomology.FormalFunctions.ungradedSheaf_map_ungradedIncl_eval`: the degree-`i`
  inclusion of a global section of a homogeneous piece commutes with restriction.
* `Stacks.Cohomology.FormalFunctions.pushforwardRingIso_inv_app_ungradedIncl`: **the scalar
  identity over an arbitrary open.**
* `Stacks.Cohomology.FormalFunctions.reesCoprodPushforwardIso_hom`: `ε` on the nose.
* `Stacks.Cohomology.FormalFunctions.reesSmulCompatible`: **the sheaf-level identity.**

## Implementation notes

The three categories in play — `X.left.Modules`, the `⨁ₙ ℐⁿ`-modules and the quasi-coherent full
subcategory — have definitionally equal but syntactically different spellings of their rings of
sections (`AlgebraSheaf.ringSheaf (reesAlgebraSheaf ℐ)` against
`(baseReesAlgebra I X).ungradedSheaf`, `Scheme.ringCatSheaf` against
`Sheaf (Opens.grothendieckTopology _) RingCat`). Instance resolution and `simp` are syntactic, so
neither finds a scalar action across those spellings: `simp only [Category.assoc]` fails on a
goal in `X.left.Modules` with a type-correctness error, and `t • w` does not elaborate when `t`
and `w` are written in different spellings. The proof therefore (a) states its section-level
lemma `rees_smul_key` entirely in the `(baseReesAlgebra I X).ungradedSheaf` spelling, which is
the one the coproduct comparison's lemmas use, (b) forces the other spelling where it is needed
with `id (α := _)`, which — unlike a type ascription `(w : _)` — really does change the type the
elaborator sees, and (c) does its re-associations in `rees_assemble`, stated in an abstract
category where `simp` works.

`reesSmulCompatible` rewrites with `reesCoprodPushforwardIso_hom` before anything else: left to
unfold `ε` itself, unification runs out of heartbeats.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology
open Stacks.Cohomology.AffineBase Stacks.Blowup
open scoped DirectSum

universe v₁ u₁ u

namespace Stacks.Cohomology.FormalFunctions

/-! ### Two lemmas in an abstract category -/

/-- Transport of `F.map` along an equality of functors: the two images of a morphism differ by
the identifications of their sources and targets. -/
private theorem map_eqToHom_of_functor_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₁}
    [Category.{v₁} D] {F₁ F₂ : C ⥤ D} (hF : F₁ = F₂) {G G' : C} (ψ : G ⟶ G')
    (h : F₁.obj G = F₂.obj G) (h' : F₁.obj G' = F₂.obj G') :
    F₁.map ψ ≫ eqToHom h' = eqToHom h ≫ F₂.map ψ := by
  subst hF
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The re-association that assembles the sheaf-level identity out of the identity before the
object identification and the commutation of the multiplication with that identification. It is
stated in an abstract category because in `X.left.Modules` the two spellings of the structure
sheaf make `simp only [Category.assoc]` fail on a type-correctness check. -/
public theorem rees_assemble {C : Type u₁} [Category.{v₁} C] {o p q s x y : C}
    {a : o ⟶ p} {i1 : p ⟶ q} {i0 : o ⟶ q} {c : q ⟶ s} {r : s ⟶ x} {T : x ⟶ x}
    {e : x ⟶ y} {P : y ⟶ y}
    (hL : a ≫ i1 ≫ c ≫ r = (i0 ≫ c ≫ r) ≫ T) (he : T ≫ e = e ≫ P) :
    a ≫ i1 ≫ c ≫ r ≫ e = i0 ≫ (c ≫ r ≫ e) ≫ P := by
  have h1 : a ≫ i1 ≫ c ≫ r ≫ e = (a ≫ i1 ≫ c ≫ r) ≫ e := by
    simp only [Category.assoc]
  rw [h1, hL, Category.assoc, he]
  simp only [Category.assoc]

/-! ### [Stacks, Tag 01SB]'s functor is the direct image -/

/-- **[Stacks, Tag 01SB]'s equivalence, followed by restriction of scalars along the structure
map of the algebra, is the direct image** — as an equality of functors. This is the functor-level
form of
`Stacks.Cohomology.FormalFunctions.restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj`
and is proved the same way: the equivalence's functor is the direct image of modules with the
`π_* 𝒪`-structure transported along [Stacks, Tag 01LX] part (3), restriction of scalars along a
composite is the composite of restrictions, and the composite scalar map is `π^♯`. -/
public theorem restrictScalars_relativeSpecQcohEquivalence_functor
    {S : Scheme.{u}} (𝒜 : AlgebraSheaf S) [AlgebraSheaf.IsQuasicoherent 𝒜] :
    (relativeSpecQcohEquivalence 𝒜).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent (AlgebraSheaf.ringSheaf 𝒜)) ⋙
        SheafOfModules.restrictScalars (AlgebraSheaf.structureMap 𝒜) =
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (relativeSpec 𝒜).ringCatSheaf) ⋙
        AlgebraicGeometry.Scheme.Modules.pushforward (relativeSpecToBase 𝒜) := by
  have hmap : AlgebraSheaf.structureMap 𝒜 ≫ (pushforwardRingIso 𝒜).inv =
      (relativeSpecToBase 𝒜).toRingCatSheafHom :=
    (Iso.comp_inv_eq _).2 (structureMap_comp_pushforwardRingIso 𝒜).symm
  show (ObjectProperty.ι (SheafOfModules.isQuasicoherent (relativeSpec 𝒜).ringCatSheaf) ⋙
      Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules
        (relativeSpecToBase 𝒜).base (relativeSpec 𝒜).ringCatSheaf ⋙
      SheafOfModules.restrictScalars
        (AlgebraSheaf.structureMap 𝒜 ≫ (pushforwardRingIso 𝒜).inv)) = _
  exact congrArg (fun α => ObjectProperty.ι
      (SheafOfModules.isQuasicoherent (relativeSpec 𝒜).ringCatSheaf) ⋙
    Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules
      (relativeSpecToBase 𝒜).base (relativeSpec 𝒜).ringCatSheaf ⋙
    SheafOfModules.restrictScalars α) hmap

/-- **The direct image of a morphism of quasi-coherent modules on the relative spectrum is the
restriction of scalars of its image under [Stacks, Tag 01SB]'s equivalence**, between the
identifications of the two objects. -/
public theorem restrictScalars_relativeSpecQcohEquivalence_functor_map
    {S : Scheme.{u}} (𝒜 : AlgebraSheaf S) [AlgebraSheaf.IsQuasicoherent 𝒜]
    {G G' : (SheafOfModules.isQuasicoherent (relativeSpec 𝒜).ringCatSheaf).FullSubcategory}
    (ψ : G ⟶ G') :
    (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap 𝒜)).map
          ((ObjectProperty.ι _).map ((relativeSpecQcohEquivalence 𝒜).functor.map ψ)) ≫
        eqToHom (restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj 𝒜 G') =
      eqToHom (restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj 𝒜 G) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (relativeSpecToBase 𝒜)).map
          ((ObjectProperty.ι _).map ψ) :=
  map_eqToHom_of_functor_eq (restrictScalars_relativeSpecQcohEquivalence_functor 𝒜) ψ _ _

section Rees

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-! ### The section of `⨁ₙ ℐⁿ` by which a homogeneous element of `B` acts -/

/-- **The degree-`i` inclusion of a global section of `ℐⁱ` commutes with restriction**: the
section it names in `⨁ₙ ℐⁿ` over a smaller open is the inclusion of its restriction. -/
public theorem ungradedSheaf_map_ungradedIncl_eval
    (i : ℤ) (s : ((baseReesAlgebra I X).piece i).val.sections)
    {U V : (Opens X.left)ᵒᵖ} (f : U ⟶ V) :
    ((baseReesAlgebra I X).ungradedSheaf.obj.map f).hom
        ((baseReesAlgebra I X).ungradedIncl i (s.eval U)) =
      (baseReesAlgebra I X).ungradedIncl i (s.eval V) := by
  refine Eq.trans ((baseReesAlgebra I X).toPresheafGradedAlgebra.totalSheafRestrict_inclSheaf
    (J := Opens.grothendieckTopology X.left) f i (s.eval U)) ?_
  exact congrArg ((baseReesAlgebra I X).ungradedIncl i)
    (PresheafOfModules.sections_property s f)

/-- **The scalar identity, over an arbitrary open.** Through [Stacks, Tag 01LX] part (3), the
degree-`k` inclusion of the section of `ℐᵏ` attached to a homogeneous `b ∈ Iᵏ` is the function on
`X'` by which `b` acts on every `𝒪_{X'}`-module. Over `⊤` this is
`Stacks.Cohomology.FormalFunctions.specAlgebraRingHom_reesSpecStructure_reesGrading`; both sides
are restrictions of their values over `⊤`, the left by
`Stacks.Cohomology.FormalFunctions.ungradedSheaf_map_ungradedIncl_eval` and naturality, the right
by the definition of `AlgebraicGeometry.baseRingToSections`. -/
public theorem pushforwardRingIso_inv_app_ungradedIncl (k : ℕ) (b : ↥(reesGrading I k))
    (U : (Opens X.left)ᵒᵖ) :
    ((pushforwardRingIso (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.hom.app U).hom
        ((baseReesAlgebra I X).ungradedIncl (k : ℤ) ((gradedReesSection I X b).eval U)) =
      AlgebraicGeometry.baseRingToSections ↥(reesAlgebra I)
        (Over.mk (reesSpecStructure I X))
        (op ((reesRelativeSpec I X).hom ⁻¹ᵁ U.unop)) (b : ↥(reesAlgebra I)) := by
  have hres := ungradedSheaf_map_ungradedIncl_eval I X (k : ℤ) (gradedReesSection I X b)
    (U.unop.leTop.op : (op (⊤ : X.left.Opens)) ⟶ U)
  have hnat := NatTrans.naturality_apply
    (pushforwardRingIso (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.hom
    (U.unop.leTop.op : (op (⊤ : X.left.Opens)) ⟶ U)
    ((baseReesAlgebra I X).ungradedIncl (k : ℤ)
      ((gradedReesSection I X b).eval (op (⊤ : X.left.Opens))))
  refine Eq.trans (congrArg (fun z =>
    ((pushforwardRingIso (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.hom.app U).hom z)
    hres.symm) ?_
  refine hnat.trans ?_
  exact congrArg
    (fun z => (((Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing
      (relativeSpecToBase (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).base
      (relativeSpec (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).ringCatSheaf).obj.map
        (U.unop.leTop.op : (op (⊤ : X.left.Opens)) ⟶ U)).hom) z)
    (specAlgebraRingHom_reesSpecStructure_reesGrading I X k b).symm

variable (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X))
  (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
  (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules))

/-! ### The identity -/

/-- **`ε` on the nose**: the coproduct comparison, then the defining isomorphism of `F'`, then
the identification of [Stacks, Tag 01SB]'s functor with the direct image. -/
public theorem reesCoprodPushforwardIso_hom :
    (reesCoprodPushforwardIso I X M hqc hneg).hom =
      (SheafOfModules.GradedModule.coprodIsoUngradedSheaf M hneg).hom ≫
        (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap
            (reesAlgebraSheaf (baseIdealSheaf A I X.hom)))).map
          ((ObjectProperty.ι _).map (reesBaseChangeModuleIso I X M hqc hneg).inv) ≫
        eqToHom (restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj
          (reesAlgebraSheaf (baseIdealSheaf A I X.hom))
          ((relativeSpecQcohEquivalence
            (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inverse.obj
              (reesTotalQcoh I X M hqc hneg))) := rfl

/-- **The identity before the object identification**, for an arbitrary `⨁ₙ ℐⁿ`-linear `φ` out
of the total module and an arbitrary endomorphism `T` of its target which is multiplication by
the degree-`k` section attached to `b`.

On sections this is three steps:
`SheafOfModules.GradedModule.coprodIsoUngradedSheaf_hom_sigma_ι_smul`, which says that the
degree-`(k + n)` injection of the degreewise action is the product of the degree-`k` section with
the degree-`n` injection; `⨁ₙ ℐⁿ`-linearity of `φ`; and `hT`. -/
private theorem rees_smul_key (k n : ℕ) (b : ↥(reesGrading I k))
    {N : SheafOfModules.{u} (baseReesAlgebra I X).ungradedSheaf}
    (φ : SheafOfModules.GradedModule.ungradedSheaf M ⟶ N) (T : N ⟶ N)
    (hT : ∀ (U : (Opens X.left)ᵒᵖ) (w : (N.val.obj U : Type u)),
      T.val.app U w =
        (baseReesAlgebra I X).ungradedIncl (k : ℤ) ((gradedReesSection I X b).eval U) • w) :
    actHom I X M b (n : ℤ) (degree_add_eq k n) ≫
        Limits.Sigma.ι (fun m : ℕ => M.piece (m : ℤ)) (k + n) ≫
          (SheafOfModules.GradedModule.coprodIsoUngradedSheaf M hneg).hom ≫
          (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap
            (reesAlgebraSheaf (baseIdealSheaf A I X.hom)))).map φ =
      (Limits.Sigma.ι (fun m : ℕ => M.piece (m : ℤ)) n ≫
          (SheafOfModules.GradedModule.coprodIsoUngradedSheaf M hneg).hom ≫
          (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap
            (reesAlgebraSheaf (baseIdealSheaf A I X.hom)))).map φ) ≫
        (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap
          (reesAlgebraSheaf (baseIdealSheaf A I X.hom)))).map T := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  have hA := (SheafOfModules.GradedModule.coprodIsoUngradedSheaf_hom_sigma_ι_smul M hneg U k n
    (k + n) (degree_add_eq k n) ((gradedReesSection I X b).eval U) x).symm
  refine Eq.trans (congrArg (fun z => φ.val.app U z) hA) ?_
  refine ((φ.val.app U).hom.map_smul _ _).trans ?_
  refine Eq.trans ?_ (hT U _).symm
  exact congrArg (fun z =>
    (baseReesAlgebra I X).ungradedIncl (k : ℤ) ((gradedReesSection I X b).eval U) • z)
    (congrArg (fun y => φ.val.app U y)
      (SheafOfModules.GradedModule.coprodIsoUngradedSheaf_hom_sigma_ι M hneg U n x).symm)

/-- **The one sheaf-level identity the `B`-linearity of [Stacks, Tag 0897]'s comparison reduces
to**, at the identification `Stacks.Cohomology.FormalFunctions.reesCoprodPushforwardIso`: for `b`
homogeneous of degree `k`, the direct image of multiplication by `b` on `F'` is, through `ε`, the
degreewise action `Stacks.Cohomology.FormalFunctions.actHom` of `b` on `∐ₙ Mₙ`. -/
public theorem reesSmulCompatible :
    ReesSmulCompatible I X M (reesBaseChangeModule I X M hqc hneg)
      (reesCoprodPushforwardIso I X M hqc hneg) := by
  intro k n b
  let : Linear ↥(reesAlgebra I) (reesRelativeSpec I X).left.Modules :=
    AlgebraicGeometry.modulesLinear ↥(reesAlgebra I) (Over.mk (reesSpecStructure I X))
  rw [reesCoprodPushforwardIso_hom I X M hqc hneg]
  exact rees_assemble
      (rees_smul_key I X M hneg k n b
        ((ObjectProperty.ι _).map (reesBaseChangeModuleIso I X M hqc hneg).inv)
        ((ObjectProperty.ι _).map ((relativeSpecQcohEquivalence
          (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).functor.map
          (ObjectProperty.homMk ((b : ↥(reesAlgebra I)) • 𝟙
            (reesBaseChangeModule I X M hqc hneg)))))
        (by
          intro U w
          exact congrArg (fun t : (reesRelativeSpec I X).left.ringCatSheaf.obj.obj
              (op ((reesRelativeSpec I X).hom ⁻¹ᵁ U.unop)) =>
            t • id (α := ((reesBaseChangeModule I X M hqc hneg).val.obj
              (op ((reesRelativeSpec I X).hom ⁻¹ᵁ U.unop)) : Type u)) w)
            (pushforwardRingIso_inv_app_ungradedIncl I X k b U).symm))
      (restrictScalars_relativeSpecQcohEquivalence_functor_map
        (reesAlgebraSheaf (baseIdealSheaf A I X.hom))
        (ObjectProperty.homMk ((b : ↥(reesAlgebra I)) • 𝟙
          (reesBaseChangeModule I X M hqc hneg))))

/-! ### The comparison, with nothing left over -/

variable (p : ℕ) (hX : AlgebraicGeometry.IsProper X.hom)

attribute [local irreducible] Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
  reesClosedImmersion reesClosedImmersionOver

/-- **The comparison is semilinear on the generators.** -/
public theorem reesCmpAddEquiv_smul_of (k n : ℕ) (b : ↥(reesGrading I k))
    (x : gradedCohomologyPiece I X M p n) :
    letI := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
    reesCmpAddEquiv I X M p (reesBaseChangeModule I X M hqc hneg) hX
        (reesCoprodPushforwardIso I X M hqc hneg)
        (DirectSum.of (gradedCohomologyPiece I X M p) (k + n)
          (gradedCohomologySmul I X M p b x)) =
      specAlgebraRingHom ↥(reesAlgebra I) (reesSpecStructure I X) (b : ↥(reesAlgebra I)) •
        reesCmpAddEquiv I X M p (reesBaseChangeModule I X M hqc hneg) hX
          (reesCoprodPushforwardIso I X M hqc hneg)
          (DirectSum.of (gradedCohomologyPiece I X M p) n x) := by
  let := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
  have e2 := congrArg (fun φ : M.piece (n : ℤ) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (reesRelativeSpec I X).hom).obj
        (reesBaseChangeModule I X M hqc hneg) =>
    (((moduleGlobalSections X.left).rightDerived p).map φ).hom x)
    (reesSmulCompatible I X M hqc hneg k n b)
  have hL := (map_three X p (actHom I X M b (n : ℤ) (degree_add_eq k n))
    (Limits.Sigma.ι (fun m : ℕ => M.piece (m : ℤ)) (k + n))
    (reesCoprodPushforwardIso I X M hqc hneg).hom x).trans
    (congrArg (fun φ => ((cohomologyFunctor X p).map φ).hom x) (Category.assoc _ _ _))
  have hR := (map_three X p (Limits.Sigma.ι (fun m : ℕ => M.piece (m : ℤ)) n)
    (reesCoprodPushforwardIso I X M hqc hneg).hom
    ((AlgebraicGeometry.Scheme.Modules.pushforward (reesRelativeSpec I X).hom).map
      (let : Linear ↥(reesAlgebra I) (reesRelativeSpec I X).left.Modules :=
         AlgebraicGeometry.modulesLinear ↥(reesAlgebra I) (Over.mk (reesSpecStructure I X))
       (b : ↥(reesAlgebra I)) • 𝟙 (reesBaseChangeModule I X M hqc hneg))) x).trans
    (congrArg (fun φ => ((cohomologyFunctor X p).map φ).hom x) (Category.assoc _ _ _))
  refine (reesCmpAddEquiv_of I X M p (reesBaseChangeModule I X M hqc hneg) hX
    (reesCoprodPushforwardIso I X M hqc hneg) (k + n)
    (gradedCohomologySmul I X M p b x)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z =>
      specAlgebraRingHom ↥(reesAlgebra I) (reesSpecStructure I X) (b : ↥(reesAlgebra I)) • z)
    (reesCmpAddEquiv_of I X M p (reesBaseChangeModule I X M hqc hneg) hX
      (reesCoprodPushforwardIso I X M hqc hneg) n x)).symm
  refine Eq.trans ?_
    (smul_cohomologyIsoPushforward_inv I X p (reesBaseChangeModule I X M hqc hneg)
      (b : ↥(reesAlgebra I)) _).symm
  exact congrArg (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
    (reesRelativeSpec I X).hom (reesBaseChangeModule I X M hqc hneg) p).inv.hom
    (hL.trans (e2.trans hR.symm))

attribute [local instance] cohomologyGradedModule

/-- **The comparison is `⨁ₖ Iᵏ`-semilinear**: both sides are additive in the scalar and in the
argument, so the generators suffice. -/
public theorem reesCmpAddEquiv_smul (c : ⨁ k, ↥(reesGrading I k))
    (y : ⨁ n : ℕ, gradedCohomologyPiece I X M p n) :
    letI := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
    reesCmpAddEquiv I X M p (reesBaseChangeModule I X M hqc hneg) hX
        (reesCoprodPushforwardIso I X M hqc hneg) (c • y) =
      specAlgebraRingHom ↥(reesAlgebra I) (reesSpecStructure I X)
          ((DirectSum.decomposeRingEquiv (reesGrading I)).symm c) •
        reesCmpAddEquiv I X M p (reesBaseChangeModule I X M hqc hneg) hX
          (reesCoprodPushforwardIso I X M hqc hneg) y := by
  let := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
  induction c using DirectSum.induction_on with
  | zero => simp
  | of k b =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | of n x =>
          rw [DirectSum.Gmodule.of_smul_of]
          refine Eq.trans (reesCmpAddEquiv_smul_of I X M hqc hneg p hX k n b x) ?_
          exact congrArg (fun r => specAlgebraRingHom ↥(reesAlgebra I) (reesSpecStructure I X) r •
            reesCmpAddEquiv I X M p (reesBaseChangeModule I X M hqc hneg) hX
              (reesCoprodPushforwardIso I X M hqc hneg)
              (DirectSum.of (gradedCohomologyPiece I X M p) n x))
            (DirectSum.decompose_symm_of (reesGrading I) b).symm
      | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
  | add c c' hc hc' => simp only [add_smul, map_add, hc, hc']

/-- **The `B`-linear comparison `cmp` of [Stacks, Tag 0897]**, with no hypothesis left. -/
public def reesCmp :
    letI := gradedCohomologySumModuleRees I X M p hneg
    letI := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
    gradedCohomologySum M p ≃ₗ[↥(reesAlgebra I)]
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom ↥(reesAlgebra I)
          (reesSpecStructure I X))).obj
        (cohomologyOf (reesRelativeSpec I X).left p
          (reesBaseChangeModule I X M hqc hneg))) :=
  letI := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
  letI := gradedCohomologySumModule I X M p hneg
  letI := gradedCohomologySumModuleRees I X M p hneg
  AddEquiv.toLinearEquiv
    ((natIntSumEquiv I X M p hneg).symm.trans
      (reesCmpAddEquiv I X M p (reesBaseChangeModule I X M hqc hneg) hX
        (reesCoprodPushforwardIso I X M hqc hneg)))
    (fun r z => by
      change reesCmpAddEquiv I X M p (reesBaseChangeModule I X M hqc hneg) hX
          (reesCoprodPushforwardIso I X M hqc hneg)
          ((natIntSumEquiv I X M p hneg).symm
            (DirectSum.decomposeRingEquiv (reesGrading I) r • z)) = _
      rw [moduleOfAddEquiv_symm_smul, reesCmpAddEquiv_smul I X M hqc hneg p hX,
        RingEquiv.symm_apply_apply]
      rfl)

include hqc hneg hX

/-- **[Stacks, Tag 02O8]'s hypothesis `h0897` at one graded module**, with everything of
[Stacks, Tag 0897]'s base change discharged. -/
public theorem isCohomologyReesFiniteOfGradedModule [IsNoetherianRing A]
    (hft : M.IsFiniteType) :
    IsCohomologyReesFiniteOfGradedModule I X M p :=
  have := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
  have := isCoherent_reesBaseChangeModule I X M hX hqc hft hneg
  isCohomologyReesFiniteOfGradedModule_of_closedImmersion I X M p hX hqc hft hneg
    (reesClosedImmersion I X) (isClosedImmersion_reesClosedImmersion I X)
    (reesBaseChangeModule I X M hqc hneg)
    (reesCmp I X M hqc hneg p hX)

end Rees

end Stacks.Cohomology.FormalFunctions

end
