module

public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.CyclicClassifyingStackPointwise
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalObjectCovering

/-!
# Global sections on `[S/(ℤ/pℤ)]` and on its pointwise quotient

Let `G : C ⥤ D` be a locally full, cover-dense functor of sites. Restricting a compatible family
of sections of a sheaf `ℱ` on `D` to the objects `G(Y)` is a bijection onto the compatible
families of `G.op ⋙ ℱ`: two global sections agreeing on the images of `G` agree (they agree
locally), and a family on the images of `G` glues
(`CategoryTheory.Functor.IsCoverDense.Types.presheafHom`). For the dense subsite
`[S/_p(ℤ/pℤ)] ⥤ [S/(ℤ/pℤ)]` and a sheaf of modules `M`, this identifies the global sections of
`M` with those of its restriction, linearly over `Γ(S, 𝒪_S)`, naturally in `M`.

## Main results

* `CategoryTheory.Functor.IsCoverDense.bijective_sectionsRestrict`: global sections restrict
  bijectively to a dense subsite.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwiseSectionsIso`: the global sections
  of a module on `[S/(ℤ/pℤ)]` are those of its restriction to the pointwise quotient.

## References

* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules

universe w v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor.IsCoverDense

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (K : GrothendieckTopology D) (ℱ : Sheaf K (Type w))

/-- Restriction of a global section of `ℱ` to the objects `G(Y)`, as a compatible family of
sections of `G.op ⋙ ℱ`. -/
def sectionsRestrict (s : ℱ.obj.sections) : (G.op ⋙ ℱ.obj).sections :=
  ⟨fun Y => s.val (op (G.obj Y.unop)), fun {_ _} g => s.property (G.op.map g)⟩

/-- The component at `Y` of the restriction of `s` is its component at `G(Y)`. -/
@[simp]
theorem sectionsRestrict_val (s : ℱ.obj.sections) (Y : Cᵒᵖ) :
    (sectionsRestrict G K ℱ s).val Y = s.val (op (G.obj Y.unop)) :=
  rfl

/-- **Global sections are compatible families on a dense subsite.** For a locally full,
cover-dense `G`, restriction of global sections of a sheaf `ℱ` to the objects `G(Y)` is a
bijection onto the compatible families of `G.op ⋙ ℱ`. -/
theorem bijective_sectionsRestrict [G.IsCoverDense K] [G.IsLocallyFull K] :
    Function.Bijective (sectionsRestrict G K ℱ) := by
  refine ⟨fun s t h => Subtype.ext (funext fun X => IsCoverDense.ext G ℱ X.unop fun Y f => ?_),
    fun s => ?_⟩
  · rw [s.property f.op, t.property f.op]
    exact congrFun (congrArg Subtype.val h) (op Y)
  · let α : G.op ⋙ (Functor.const Dᵒᵖ).obj PUnit.{w + 1} ⟶ G.op ⋙ ℱ.obj :=
      { app := fun Y => ↾fun _ => s.val Y
        naturality := fun {Y Y'} g => by
          ext
          exact (s.property g).symm }
    refine ⟨⟨fun X => (Types.presheafHom α).app X PUnit.unit, fun {X X'} g => ?_⟩,
      Subtype.ext (funext fun Y => ?_)⟩
    · exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
        ((Types.presheafHom α).naturality g)) PUnit.unit).symm
    · have h := Types.appHom_restrict α (𝟙 (op (G.obj Y.unop))) PUnit.unit
      simp only [CategoryTheory.Functor.map_id_apply] at h
      exact h

end CategoryTheory.Functor.IsCoverDense

namespace Stacks.Examples.UnboundedDerivedPushforward

/-- The sheaf of sets underlying a sheaf of modules. -/
def sheafOfModulesTypeSheaf {C : Type u₁} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) : Sheaf J (Type u) :=
  ⟨M.val.presheaf ⋙ forget AddCommGrpCat, (isSheaf_iff_isSheaf_of_type _ _).2
    (Presieve.isSheaf_iso J (Functor.isoWhiskerLeft M.val.presheaf
      AddCommGrpCat.coyonedaObjIsoForget) (M.isSheaf (AddCommGrpCat.of (ULift.{u} ℤ))))⟩

variable (p : ℕ) [NeZero p] {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- The restriction of a global section of a module on `[S/(ℤ/pℤ)]` to the pointwise quotient,
`Γ(S, 𝒪_S)`-linearly. -/
def cyclicPointwiseSectionsRestrict (M : SheafOfModules.{u} (cyclicStackRing p 𝒞 hS)) :
    (Stacks.CechTop.globalSectionsOverBase (cyclicStackRing p 𝒞 hS)
        (cyclicStackBaseRingHom p 𝒞 hS)).obj M →ₗ[cyclicBaseRing 𝒞 hS]
      (Stacks.CechTop.globalSectionsOverBase (cyclicPointwiseRing p 𝒞 hS)
        (cyclicPointwiseBaseRingHom p 𝒞 hS)).obj ((cyclicPointwiseRestriction p 𝒞 hS).obj M) where
  toFun s := Functor.IsCoverDense.sectionsRestrict (cyclicPointwiseInclusion p 𝒞 hS)
    (cyclicStackTopology p 𝒞 hS) (sheafOfModulesTypeSheaf M) s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The restriction of global sections to the pointwise quotient is bijective.** -/
theorem bijective_cyclicPointwiseSectionsRestrict
    (M : SheafOfModules.{u} (cyclicStackRing p 𝒞 hS)) :
    Function.Bijective (cyclicPointwiseSectionsRestrict p 𝒞 hS M) :=
  haveI := Functor.IsDenseSubsite.isCoverDense (cyclicPointwiseTopology p 𝒞 hS)
    (cyclicStackTopology p 𝒞 hS) (cyclicPointwiseInclusion p 𝒞 hS)
  haveI := Functor.IsDenseSubsite.isLocallyFull (cyclicPointwiseTopology p 𝒞 hS)
    (cyclicStackTopology p 𝒞 hS) (cyclicPointwiseInclusion p 𝒞 hS)
  Functor.IsCoverDense.bijective_sectionsRestrict (cyclicPointwiseInclusion p 𝒞 hS)
    (cyclicStackTopology p 𝒞 hS) (sheafOfModulesTypeSheaf M)

/-- **The global sections of a module on `[S/(ℤ/pℤ)]` are those of its restriction to the
pointwise quotient**, linearly over `Γ(S, 𝒪_S)` and naturally in the module. -/
def cyclicPointwiseSectionsIso :
    Stacks.CechTop.globalSectionsOverBase (cyclicStackRing p 𝒞 hS)
        (cyclicStackBaseRingHom p 𝒞 hS) ≅
      cyclicPointwiseRestriction p 𝒞 hS ⋙
        Stacks.CechTop.globalSectionsOverBase (cyclicPointwiseRing p 𝒞 hS)
          (cyclicPointwiseBaseRingHom p 𝒞 hS) :=
  NatIso.ofComponents
    (fun M => (LinearEquiv.ofBijective (cyclicPointwiseSectionsRestrict p 𝒞 hS M)
      (bijective_cyclicPointwiseSectionsRestrict p 𝒞 hS M)).toModuleIso)
    (fun _ => rfl)

/-- The isomorphism `cyclicPointwiseSectionsIso` restricts a global section to the objects of
the pointwise quotient. -/
theorem cyclicPointwiseSectionsIso_hom_app_apply (M : SheafOfModules.{u} (cyclicStackRing p 𝒞 hS))
    (s : (Stacks.CechTop.globalSectionsOverBase (cyclicStackRing p 𝒞 hS)
      (cyclicStackBaseRingHom p 𝒞 hS)).obj M) (Y : (cyclicPointwise p 𝒞 hS).objᵒᵖ) :
    ((cyclicPointwiseSectionsIso p 𝒞 hS).hom.app M s : ((cyclicPointwiseRestriction p 𝒞 hS).obj
      M).sections).val Y =
        (s : M.sections).val (op ((cyclicPointwiseInclusion p 𝒞 hS).obj Y.unop)) :=
  rfl

end Stacks.Examples.UnboundedDerivedPushforward
