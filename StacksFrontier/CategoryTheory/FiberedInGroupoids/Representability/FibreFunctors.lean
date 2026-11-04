module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.EquivalenceOver
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-! # Fibre functors of a representable 1-morphism are faithful

Stacks 02Y8 (Lemma 4.42.4): if a 1-morphism `F : 𝒳 ⥤ 𝒴` of categories fibred in groupoids over
`𝒞` is representable, then for every object `U` of `𝒞` the induced functor on fibre categories
`F_U : 𝒳_U ⥤ 𝒴_U` is faithful.  Only this implication is proved here, not its converse.

Structure functors are written `p : 𝒳 ⥤ 𝒞` with the base as target, matching
`CategoryTheory.Functor.IsFiberedInGroupoids` and the fibre category
`CategoryTheory.Functor.Fiber p U` (Stacks 04SE); a 1-morphism over `𝒞` is a functor `F` with
`F ⋙ q = p`.  Representability of `F` (Stacks 02Y7) says that for every 1-morphism
`G : 𝒞/U ⥤ 𝒴` over `𝒞` the projection `(𝒞/U) ×_𝒴 𝒳 ⥤ 𝒞/U` off the 2-fibre product (Stacks
02Y6) is a representable category fibred in groupoids, i.e. equivalent over its base to a slice
category `Over X` (Stacks 02Y3).  Such a fibration is fibred in setoids — its fibre categories
are thin — and faithfulness of `F_U` is read off from that thinness.

The 2-fibre product is `CategoryTheory.TwoFibreProductOver` (Stacks 0040), the product in the
2-category of categories **over `𝒞`**, whose comparison isomorphism `φ : G(a) ≅ F(x)` is required
to be vertical. Mathlib's `CategoryTheory.Limits.CategoricalPullback` is the 2-fibre product of
plain categories (Stacks 003R); it allows an arbitrary `φ`, is not a category over `𝒞`, and is
an inequivalent notion, so it cannot be used to state Stacks 02Y7.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.RepresentableMorphism

variable {𝒞 : Type*} [Category 𝒞] {𝒳 𝒴 : Type*} [Category 𝒳] [Category 𝒴]

/-- The functor `F_U : 𝒳_U ⥤ 𝒴_U` induced on fibre categories over `U` by a 1-morphism
`F : 𝒳 ⥤ 𝒴` over `𝒞` (i.e. with `F ⋙ q = p`): an object of `𝒳` over `U` is sent to `F.obj` of
it, which lies over `U` because `F` respects the structure functors. This is the functor Stacks
02Y8 asserts to be faithful. -/
noncomputable def inducedFiberFunctor (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)
    (hF : F ⋙ q = p) (U : 𝒞) : p.Fiber U ⥤ q.Fiber U :=
  Fiber.inducedFunctor (F := Fiber.fiberInclusion ⋙ F) (by
    rw [Functor.assoc, hF]
    exact Fiber.fiberInclusion_comp_eq_const)

/-- Two morphisms of the fibre `𝒳_U` have the same image under the induced functor on fibres
exactly when their images under `F` agree. -/
lemma inducedFiberFunctor_map_eq_iff (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p)
    (U : 𝒞) {a b : p.Fiber U} (ψ ψ' : a ⟶ b) :
    (inducedFiberFunctor p q F hF U).map ψ = (inducedFiberFunctor p q F hF U).map ψ' ↔
      F.map (Fiber.fiberInclusion.map ψ) = F.map (Fiber.fiberInclusion.map ψ') :=
  Subtype.ext_iff

/-- **Stacks 02Y3.** A category fibred in groupoids `s : 𝒮 ⥤ 𝒟` is *representable* when it is
equivalent over the base `𝒟` to a slice category `Over X` (`𝒟/X`) for some object `X` of `𝒟`,
i.e. when it is the fibration represented by `X`. -/
def IsRepresentableCFG {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟]
    (s : 𝒮 ⥤ 𝒟) : Prop :=
  ∃ (X : 𝒟) (E : 𝒮 ⥤ Over X), IsFibredEquivalence s (Over.forget X) E

/-- A category fibred in groupoids which is representable in the sense of Stacks 02Y3 — that is,
equivalent over the base to a slice category — is representable in the sense of
`Stacks.RepresentableMorphism.IsRepresentableCFG`. The two notions differ only in that
`IsRepresentableCFG` asks the equivalence and its quasi-inverse to preserve cartesian morphisms,
which is automatic here: by Stacks 02Y3 such a fibration is fibred in setoids, hence in groupoids,
and so is a slice, and in a category fibred in groupoids every morphism lying over a morphism of
the base is cartesian. -/
theorem isRepresentableCFG_of_isRepresentable {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟]
    (s : 𝒮 ⥤ 𝒟) (hs : StacksRepresentableCFG.IsRepresentable s) : IsRepresentableCFG s := by
  obtain ⟨X, ⟨e⟩⟩ := hs
  have hsg : s.IsFiberedInGroupoids :=
    (((StacksRepresentableCFG.representable_iff s).1 ⟨X, ⟨e⟩⟩).1).isFiberedInGroupoids
  have hslice : (Over.forget X).IsFiberedInGroupoids :=
    (StacksRepresentableCFG.over_isFiberedInSetoids X).isFiberedInGroupoids
  refine ⟨X, e.hom.functor, ⟨⟨e.hom.w, ?_⟩, e.inv.functor, ⟨e.inv.w, ?_⟩,
    ⟨e.counitIso, ?_⟩, ⟨e.unitIso.symm, ?_⟩⟩⟩
  · intro _ _ _ _ f φ _ _
    have : (Over.forget X).IsHomLift f (e.hom.functor.map φ) :=
      Functor.isHomLift_map_of_comp_eq e.hom.w f φ
    have := hslice.isStronglyCartesian_homLift f (e.hom.functor.map φ)
    infer_instance
  · intro _ _ _ _ f φ _ _
    have : s.IsHomLift f (e.inv.functor.map φ) :=
      Functor.isHomLift_map_of_comp_eq e.inv.w f φ
    have := hsg.isStronglyCartesian_homLift f (e.inv.functor.map φ)
    infer_instance
  · intro w
    have happ := congrArg (fun (n : _) => n.app w) e.counit_over
    simp only [Functor.whiskerRight_app, eqToHom_app] at happ
    exact ⟨_, happ⟩
  · refine NatTrans.IsOver.inv s e.unitIso ?_
    intro a
    have happ := congrArg (fun (n : _) => n.app a) e.unit_over
    simp only [Functor.whiskerRight_app, eqToHom_app] at happ
    exact ⟨_, happ⟩

/-- **Stacks 02Y7.** `F : 𝒳 ⥤ 𝒴` (a 1-morphism over `𝒞`) is *representable*, equivalently
`𝒳` is *relatively representable over* `𝒴`, when for every object `U` of `𝒞` and every
1-morphism `G : 𝒞/U ⥤ 𝒴` over `𝒞` (i.e. `G ⋙ q = Over.forget U`), the first projection
`(𝒞/U) ×_𝒴 𝒳 ⥤ 𝒞/U` of the 2-fibre product over `𝒞` is a representable category fibred in
groupoids.

The source states this for `𝒳`, `𝒴` fibred in groupoids over `𝒞`; the predicate here does
not assume that, so it is the same condition stated for an arbitrary 1-morphism and
specialises to the source's notion. -/
@[stacks 02Y7]
def IsRepresentableMorphism (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : Prop :=
  ∀ (U : 𝒞) (G : Over U ⥤ 𝒴), G ⋙ q = Over.forget U →
    IsRepresentableCFG (TwoFibreProductOver.fst (Over.forget U) p q G F)

/-!
### Reduction of `F_U` faithfulness to faithfulness of `F` on fibre morphisms

The faithfulness of the induced functor `F_U : 𝒳_U ⥤ 𝒴_U` is equivalent to the
statement that `F` is injective on morphisms of `𝒳` lying over `𝟙 U` (i.e. on
morphisms of the fibre category `𝒳_U`, viewed inside `𝒳` via `fiberInclusion`).
This part is entirely formal: it does not use representability.
-/

/-- Two morphisms over `𝟙 U` are equal if their images under `Fiber.homMk` are. -/
private theorem eq_of_homMk_eq (p : 𝒳 ⥤ 𝒞) (U : 𝒞) {a b : 𝒳} (φ φ' : a ⟶ b)
    [p.IsHomLift (𝟙 U) φ] [p.IsHomLift (𝟙 U) φ'] (h : Fiber.homMk p U φ = Fiber.homMk p U φ') :
    φ = φ' := by
  have := congrArg Fiber.fiberInclusion.map h
  rwa [Fiber.fiberInclusion_homMk, Fiber.fiberInclusion_homMk] at this

/-- If `F` is injective on morphisms coming from the fibre `𝒳_U` (via the fibre
inclusion), then the induced functor `F_U` is faithful.  This is the purely
formal half of Stacks 02Y8 and uses only the `Fiber` API of Mathlib. -/
theorem inducedFiberFunctor_faithful_of_fiberHom_injective
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p) (U : 𝒞)
    (key : ∀ {a b : p.Fiber U}
      (φ φ' : Fiber.fiberInclusion.obj a ⟶ Fiber.fiberInclusion.obj b),
      F.map φ = F.map φ' → φ = φ') :
    (inducedFiberFunctor p q F hF U).Faithful := by
  constructor
  intro a b ψ ψ' h
  exact Fiber.hom_ext (key _ _ ((inducedFiberFunctor_map_eq_iff p q F hF U ψ ψ').1 h))

/-- Converse of `Stacks.RepresentableMorphism.inducedFiberFunctor_faithful_of_fiberHom_injective`:
if the induced functor `F_U` on fibre categories is faithful, then `F` is injective on morphisms of
`𝒳` lying over `𝟙 U`. Together the two say that faithfulness of `F_U` *is* injectivity of `F` on
the morphisms of the fibre `𝒳_U`. Like the forward implication this is purely formal. -/
theorem fiberHom_injective_of_inducedFiberFunctor_faithful
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p) (U : 𝒞)
    (hfaith : (inducedFiberFunctor p q F hF U).Faithful) {a b : 𝒳} (φ φ' : a ⟶ b)
    (hφ : p.IsHomLift (𝟙 U) φ) (hφ' : p.IsHomLift (𝟙 U) φ') (h : F.map φ = F.map φ') : φ = φ' := by
  have := hφ
  have := hφ'
  have := hfaith
  have hmap : (inducedFiberFunctor p q F hF U).map (Fiber.homMk p U φ)
      = (inducedFiberFunctor p q F hF U).map (Fiber.homMk p U φ') := by
    rwa [inducedFiberFunctor_map_eq_iff, Fiber.fiberInclusion_homMk, Fiber.fiberInclusion_homMk]
  exact eq_of_homMk_eq p U φ φ' (Functor.Faithful.map_injective hmap)

/-!
### The representability step

The mathematical heart of Stacks 02Y8, following Stacks 02Y5/02Y3 and Comment
#11416 of 02Y8.

The argument is decomposed into two named sub-lemmas:

* `isFiberedInSetoids_of_isRepresentableCFG` — the *Stacks 02Y3 bridge*:
  a representable category fibred in groupoids (equivalent over the base to a
  slice `Over X`) is fibred in setoids, i.e. its fibre categories are *thin*
  (at most one morphism between any two objects).

* `fiberHom_injective_of_isRepresentableMorphism` — the injectivity of `F` on
  morphisms over `𝟙 U`, obtained by instantiating representability of `F` at a
  suitable classifying `G : 𝒞/U ⥤ 𝒴` and reading off thinness of the pullback
  fibre via the bridge lemma.

The main theorem then follows by combining the formal reduction
`inducedFiberFunctor_faithful_of_fiberHom_injective` with the second sub-lemma.
-/

/- **Stacks 02Y3 bridge.** If `s : 𝒮 ⥤ 𝒟` is a representable category fibred in
groupoids (equivalent, over the base `𝒟`, to a slice category `Over X`), then `s`
is fibred in setoids: for every `V` and every pair of parallel morphisms `f g` in
the fibre category `s.Fiber V` we have `f = g`.

Mathematically: the structure functor `Over.forget X : Over X ⥤ 𝒟` is fibred in
setoids — its fibre over `V` consists of objects `Y ⟶ X` lying over `V`, and a
morphism between two such is uniquely determined (it is a morphism in `𝒟` already
pinned by the triangle commuting over `V`), so `(Over X)_V` is thin.  An
equivalence over the base `𝒟` (the data packaged in `IsFibredEquivalence`,
including a quasi-inverse cartesian over `𝒟` and the unit/counit natural isos over
`𝒟`) induces, fibrewise over each `V`, an equivalence of fibre categories
`s.Fiber V ≃ (Over X).Fiber V`.  Thinness of the target fibre transfers along this
fibrewise equivalence to thinness of `s.Fiber V`, which is exactly
`s.IsFiberedInSetoids`. -/
namespace SliceEquivalence

/-- A morphism whose image under `p` is an `eqToHom` lies over the identity. -/
theorem ishomlift_id_of_map_eqToHom {𝒞 𝒳 : Type*} [Category 𝒞] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒞) {a b : 𝒳} (g : a ⟶ b) (h : p.obj a = p.obj b)
    (hg : p.map g = eqToHom h) : p.IsHomLift (𝟙 (p.obj a)) g := by
  apply CategoryTheory.IsHomLift.of_fac' p (𝟙 (p.obj a)) g rfl h.symm
  rw [hg]; simp

/-- Naturality decomposition for the unit/counit iso of the equivalence over the base. -/
theorem keyy {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (X : 𝒟)
    (E : 𝒮 ⥤ Over X) (G : Over X ⥤ 𝒮) (η : G ⋙ E ≅ 𝟭 (Over X))
    (a : 𝒮) (y' : Over X) (φ' : y' ⟶ E.obj a) :
    (G ⋙ E).map φ' = η.hom.app y' ≫ φ' ≫ η.inv.app (E.obj a) := by
  have hnat := η.hom.naturality φ'
  simp only [Functor.id_map] at hnat
  rw [← cancel_mono (η.hom.app (E.obj a))]
  simpa using hnat

-- suggested change: the four lemmas `keyy`, `bridge`, `hominv_over`, `emap_eps_over`,
-- `core_lift` and `s_unique_lift` below re-derive
-- `StacksRepresentableCFG.exists_lift_of_equivalenceOver` and
-- `.unique_lift_of_equivalenceOver`
-- (CategoryTheory/FiberedInGroupoids/Representability/Criterion.lean, already imported). They
-- are not a drop-in substitution: those take an `EquivalenceOver`, whose unit and counit are
-- 2-cells over the base by construction, whereas these take `E.IsEquivalence` plus separate
-- `NatTrans.IsOver` witnesses. Deduplicating means building an `EquivalenceOver` from
-- `IsFibredEquivalence` first.
/-- Transfer of `IsHomLift` from `Over.forget X` (via `E`) to `s = E ⋙ Over.forget X`. -/
theorem bridge {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (s : 𝒮 ⥤ 𝒟)
    (X : 𝒟) (E : 𝒮 ⥤ Over X) (hcomm : E ⋙ Over.forget X = s)
    {V U : 𝒟} (f : V ⟶ U) {a b : 𝒮} (φ : a ⟶ b)
    (h : (Over.forget X).IsHomLift f (E.map φ)) : s.IsHomLift f φ := by
  have hobj_a : s.obj a = (Over.forget X).obj (E.obj a) := by rw [← hcomm]; rfl
  have hobj_b : s.obj b = (Over.forget X).obj (E.obj b) := by rw [← hcomm]; rfl
  apply CategoryTheory.IsHomLift.of_fac' s f φ (R := V) (S := U) ?_ ?_ ?_
  · rw [hobj_a]; exact (CategoryTheory.IsHomLift.domain_eq (Over.forget X) f (E.map φ))
  · rw [hobj_b]; exact (CategoryTheory.IsHomLift.codomain_eq (Over.forget X) f (E.map φ))
  · have hcong := Functor.congr_hom hcomm.symm φ
    rw [hcong]
    have hfac := CategoryTheory.IsHomLift.fac' (Over.forget X) f (E.map φ)
    simp only [Functor.comp_map]
    rw [hfac]; simp

/-- The inverse of an over-the-base natural iso is itself over the base. -/
theorem hominv_over {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (X : 𝒟)
    (G : Over X ⥤ 𝒮) (E : 𝒮 ⥤ Over X) (η : G ⋙ E ≅ 𝟭 (Over X))
    (hη : NatTrans.IsOver (Over.forget X) η.hom) (w : Over X) :
    ∃ h, (Over.forget X).map (η.inv.app w) = eqToHom h :=
  NatTrans.IsOver.inv (Over.forget X) η hη w

/-- `E.map (ε.hom.app a)` is over the identity (the counit is over the base). -/
theorem emap_eps_over {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (s : 𝒮 ⥤ 𝒟)
    (X : 𝒟) (E : 𝒮 ⥤ Over X) (G : Over X ⥤ 𝒮) (hcomm : E ⋙ Over.forget X = s)
    (ε : E ⋙ G ≅ 𝟭 𝒮) (hε : NatTrans.IsOver s ε.hom) (a : 𝒮) :
    ∃ h, (Over.forget X).map (E.map (ε.hom.app a)) = eqToHom h := by
  obtain ⟨hh3, he3⟩ := hε a
  have hcg := Functor.congr_hom hcomm (ε.hom.app a)
  simp only [Functor.comp_map] at hcg
  rw [he3] at hcg
  rw [eqToHom_trans, eqToHom_trans] at hcg
  exact ⟨_, hcg⟩

/-- The cartesian lift `φ'` in the slice, transported through `G` and the counit, remains a
lift of `f` after applying `E`. -/
theorem core_lift {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (s : 𝒮 ⥤ 𝒟)
    (X : 𝒟) (E : 𝒮 ⥤ Over X) (hcomm : E ⋙ Over.forget X = s)
    (G : Over X ⥤ 𝒮) (η : G ⋙ E ≅ 𝟭 (Over X)) (hη : NatTrans.IsOver (Over.forget X) η.hom)
    (ε : E ⋙ G ≅ 𝟭 𝒮) (hε : NatTrans.IsOver s ε.hom)
    {V U : 𝒟} (f : V ⟶ U) (a : 𝒮) (y' : Over X) (φ' : y' ⟶ E.obj a)
    (hφ' : (Over.forget X).IsHomLift f φ') :
    (Over.forget X).IsHomLift f (E.map (G.map φ' ≫ ε.hom.app a)) := by
  let q := Over.forget X
  have hcomp : E.map (G.map φ' ≫ ε.hom.app a)
      = η.hom.app y' ≫ φ' ≫ (η.inv.app (E.obj a) ≫ E.map (ε.hom.app a)) := by
    rw [E.map_comp, show E.map (G.map φ') = (G ⋙ E).map φ' from rfl, keyy X E G η a y' φ']
    simp
  rw [hcomp]
  obtain ⟨hh1, he1⟩ := hη y'
  have inst1 := ishomlift_id_of_map_eqToHom q (η.hom.app y') hh1 he1
  obtain ⟨hh2, he2⟩ := hominv_over X G E η hη (E.obj a)
  obtain ⟨hh3, he3⟩ := emap_eps_over s X E G hcomm ε hε a
  have heInner : q.map (η.inv.app (E.obj a) ≫ E.map (ε.hom.app a)) = eqToHom (hh2.trans hh3) := by
    rw [Functor.map_comp, he2, he3, eqToHom_trans]
  have instInner0 :=
    ishomlift_id_of_map_eqToHom q (η.inv.app (E.obj a) ≫ E.map (ε.hom.app a)) _ heInner
  have hUeq : q.obj ((𝟭 (Over X)).obj (E.obj a)) = U := CategoryTheory.IsHomLift.codomain_eq q f φ'
  have instInner : q.IsHomLift (𝟙 U) (η.inv.app (E.obj a) ≫ E.map (ε.hom.app a)) := by
    rw [← hUeq]; exact instInner0
  have instMid : q.IsHomLift f (φ' ≫ (η.inv.app (E.obj a) ≫ E.map (ε.hom.app a))) :=
    CategoryTheory.IsHomLift.comp_lift_id_right q f φ' (η.inv.app (E.obj a) ≫ E.map (ε.hom.app a))
  have hVeq : q.obj ((G ⋙ E).obj y') = V := by
    rw [hh1]; exact CategoryTheory.IsHomLift.domain_eq q f φ'
  have inst1' : q.IsHomLift (𝟙 V) (η.hom.app y') := by
    rw [← hVeq]; exact inst1
  exact CategoryTheory.IsHomLift.comp_lift_id_left q f
    (φ' ≫ (η.inv.app (E.obj a) ≫ E.map (ε.hom.app a))) (η.hom.app y')

/-- Build the quasi-inverse equivalence `𝒮 ≌ Over X` from `IsFibredEquivalence`. -/
theorem isEquivalence_of_isEquivalenceOver {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟]
    (s : 𝒮 ⥤ 𝒟) (X : 𝒟) (E : 𝒮 ⥤ Over X) (hE : IsFibredEquivalence s (Over.forget X) E) :
    E.IsEquivalence := by
  obtain ⟨G, hGcart, ⟨η, hη⟩, ⟨ε, hε⟩⟩ := hE.exists_inverse
  exact (CategoryTheory.Equivalence.mk E G ε.symm η).isEquivalence_functor

/-- `unique_lift` for `s`, transferred from `Over.forget X` along the equivalence `E`. -/
theorem s_unique_lift {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (s : 𝒮 ⥤ 𝒟)
    (X : 𝒟) (E : 𝒮 ⥤ Over X) (hcomm : E ⋙ Over.forget X = s) [E.IsEquivalence]
    (hfgU : (Over.forget X).IsFiberedInGroupoids)
    {x y z : 𝒮} (φ : y ⟶ x) (ψ : z ⟶ x) (f : s.obj z ⟶ s.obj y)
    (hf : f ≫ s.map φ = s.map ψ) :
    ∃! χ, s.map χ = f ∧ χ ≫ φ = ψ := by
  have hmap : ∀ {u v : 𝒮} (g : u ⟶ v), s.map g
      = eqToHom (Functor.congr_obj hcomm u).symm ≫ (Over.forget X).map (E.map g)
        ≫ eqToHom (Functor.congr_obj hcomm v) := by
    intro u v g
    simpa only [comp_obj, Over.forget_obj, Functor.comp_map]
      using Functor.congr_hom hcomm.symm g
  have hmap2 : ∀ {u v : 𝒮} (g : u ⟶ v), (Over.forget X).map (E.map g)
      = eqToHom (Functor.congr_obj hcomm u) ≫ s.map g
        ≫ eqToHom (Functor.congr_obj hcomm v).symm := by
    intro u v g
    rw [hmap g]
    simp [Category.assoc]
  set ez := Functor.congr_obj hcomm z
  set ey := Functor.congr_obj hcomm y
  set ex := Functor.congr_obj hcomm x
  set f' : (Over.forget X).obj (E.obj z) ⟶ (Over.forget X).obj (E.obj y) :=
    eqToHom ez ≫ f ≫ eqToHom ey.symm with hf'def
  have hf2 : f' ≫ (Over.forget X).map (E.map φ) = (Over.forget X).map (E.map ψ) := by
    have key := hf
    rw [hmap φ, hmap ψ] at key
    rw [hf'def, ← cancel_epi (eqToHom ez.symm), ← cancel_mono (eqToHom ex)]
    simp only [Category.assoc, eqToHom_refl, Category.id_comp, eqToHom_trans_assoc] at key ⊢
    simpa [Category.assoc] using key
  obtain ⟨χ', ⟨hχ'₁, hχ'₂⟩, hχ'uniq⟩ := hfgU.unique_lift (E.map φ) (E.map ψ) f' hf2
  have cond_mp : ∀ χ : z ⟶ y, (s.map χ = f ∧ χ ≫ φ = ψ)
      → ((Over.forget X).map (E.map χ) = f' ∧ E.map χ ≫ E.map φ = E.map ψ) := by
    rintro χ ⟨h₁, h₂⟩
    exact ⟨by rw [hmap2 χ, h₁, hf'def], by rw [← E.map_comp, h₂]⟩
  have cond_mpr : ∀ χ : z ⟶ y,
      ((Over.forget X).map (E.map χ) = f' ∧ E.map χ ≫ E.map φ = E.map ψ)
      → (s.map χ = f ∧ χ ≫ φ = ψ) := by
    rintro χ ⟨h₁, h₂⟩
    refine ⟨?_, E.map_injective (by rw [E.map_comp, h₂])⟩
    rw [hmap χ, h₁, hf'def]
    simp [Category.assoc]
  refine ⟨E.preimage χ', cond_mpr _ ⟨by rwa [E.map_preimage], by rwa [E.map_preimage]⟩, ?_⟩
  refine fun χ hχ => E.map_injective ?_
  rw [E.map_preimage]
  exact hχ'uniq (E.map χ) (cond_mp χ hχ)

/-- `fiber_isThin` for `s`: the fibre categories of `s` are thin. -/
theorem s_fibers_setoid {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (s : 𝒮 ⥤ 𝒟)
    (X : 𝒟) (E : 𝒮 ⥤ Over X) (hcomm : E ⋙ Over.forget X = s) [E.IsEquivalence]
    {U : 𝒟} {a b : s.Fiber U} (f g : a ⟶ b) : f = g := by
  apply Fiber.hom_ext
  apply E.map_injective
  apply (Over.forget X).map_injective
  have hf := Functor.congr_hom hcomm (Fiber.fiberInclusion.map f)
  have hg := Functor.congr_hom hcomm (Fiber.fiberInclusion.map g)
  rw [Functor.comp_map] at hf hg
  rw [hf, hg, CategoryTheory.IsHomLift.fac' s (𝟙 U) (Fiber.fiberInclusion.map f),
      CategoryTheory.IsHomLift.fac' s (𝟙 U) (Fiber.fiberInclusion.map g)]

end SliceEquivalence

namespace ClassifyingFunctor

/-- For a functor fibred in setoids, two morphisms with the same projection are equal
(Stacks 02Y4): both `α, β` lie over the same base morphism, so by `unique_lift` there is a
unique vertical `χ` with `χ ≫ β = α`, and `fiber_isThin` forces `χ = 𝟙`, whence `α = β`. -/
theorem map_injective_of_isFiberedInSetoids
    {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (s : 𝒮 ⥤ 𝒟)
    [hs : s.IsFiberedInSetoids] {a b : 𝒮} (α β : a ⟶ b)
    (h : s.map α = s.map β) : α = β := by
  -- factor: f := 𝟙 (s.obj a), φ := β, ψ := α
  have hf : 𝟙 (s.obj a) ≫ s.map β = s.map α := by rw [Category.id_comp, h]
  obtain ⟨χ, ⟨hχmap, hχcomp⟩, _⟩ :=
    hs.isFiberedInGroupoids.unique_lift β α (𝟙 (s.obj a)) hf
  -- χ : a ⟶ a lies over 𝟙 (s.obj a)
  have hχlift : s.IsHomLift (𝟙 (s.obj a)) χ := by
    refine CategoryTheory.IsHomLift.of_fac' s (𝟙 (s.obj a)) χ rfl rfl ?_
    rw [hχmap]; simp
  -- χ = 𝟙 a via thinness of the fibre
  have hχid : χ = 𝟙 a := by
    have hthin := hs.fiber_isThin (s.obj a)
    exact eq_of_homMk_eq s (s.obj a) χ (𝟙 a)
      (Subsingleton.elim (Fiber.homMk s (s.obj a) χ) (Fiber.homMk s (s.obj a) (𝟙 a)))
  rw [← hχcomp, hχid, Category.id_comp]

/-! ### The 2-Yoneda classifying-functor construction

For `W : Over U` we choose, via `hq.exists_lift W.hom hy₀`, a cartesian pullback
`classifyingObj W` of `y₀` along `W.hom`, together with a structural morphism
`classifyingStr W : classifyingObj W ⟶ y₀` lying over `W.hom`.  The functorial
action on a morphism `h : W ⟶ W'` is the unique vertical-over-`h.left` morphism
provided by `hq.unique_lift`. -/

/-- The chosen pullback object of `y₀` along `W.hom`. -/
noncomputable def classifyingObj (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) (W : Over U) : 𝒴 :=
  (hq.exists_lift W.hom y₀ hy₀).choose

/-- The structural morphism `classifyingObj W ⟶ y₀` lying over `W.hom`. -/
noncomputable def classifyingStr (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) (W : Over U) :
    classifyingObj q hq U y₀ hy₀ W ⟶ y₀ :=
  (hq.exists_lift W.hom y₀ hy₀).choose_spec.choose

/-- The structural morphism lies over `W.hom` (this is the canonical
`IsHomLift` witness packaged by `exists_lift`). -/
theorem classifyingStr_isHomLift (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) (W : Over U) :
    q.IsHomLift W.hom (classifyingStr q hq U y₀ hy₀ W) :=
  (hq.exists_lift W.hom y₀ hy₀).choose_spec.choose_spec

/-- The chosen pullback object lies over `W.left`. -/
theorem classifyingHobj (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) (W : Over U) :
    q.obj (classifyingObj q hq U y₀ hy₀ W) = W.left :=
  have := classifyingStr_isHomLift q hq U y₀ hy₀ W
  IsHomLift.domain_eq q W.hom (classifyingStr q hq U y₀ hy₀ W)

/-- The explicit base-level form of `classifyingStr_isHomLift`: `q` sends the structural morphism
to `W.hom`, conjugated by the `eqToHom`s identifying its source with `W.left` and its target with
`U`. This is the shape needed to feed `unique_lift` in `classifyingMap`. -/
theorem classifyingStr_spec (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) (W : Over U) :
    q.map (classifyingStr q hq U y₀ hy₀ W)
      = eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ W.hom ≫ eqToHom hy₀.symm := by
  have := classifyingStr_isHomLift q hq U y₀ hy₀ W
  rw [IsHomLift.fac' q W.hom (classifyingStr q hq U y₀ hy₀ W)]

/-- The base-level factoring condition feeding `existsUnique_factor`. -/
theorem map_cond (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' : Over U} (h : W ⟶ W') :
    (eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ h.left
        ≫ eqToHom (classifyingHobj q hq U y₀ hy₀ W').symm)
      ≫ q.map (classifyingStr q hq U y₀ hy₀ W') = q.map (classifyingStr q hq U y₀ hy₀ W) := by
  rw [classifyingStr_spec, classifyingStr_spec]
  have hw : h.left ≫ W'.hom = W.hom := Over.w h
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc h.left, hw]

/-- The functorial action on a morphism `h : W ⟶ W'`. -/
noncomputable def classifyingMap (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' : Over U} (h : W ⟶ W') :
    classifyingObj q hq U y₀ hy₀ W ⟶ classifyingObj q hq U y₀ hy₀ W' :=
  (hq.unique_lift (classifyingStr q hq U y₀ hy₀ W') (classifyingStr q hq U y₀ hy₀ W)
    (eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ h.left
      ≫ eqToHom (classifyingHobj q hq U y₀ hy₀ W').symm)
    (map_cond q hq U y₀ hy₀ h)).exists.choose

/-- The `unique_lift` specification that defines `classifyingMap`. -/
private theorem classifyingMap_spec (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' : Over U} (h : W ⟶ W') :
    q.map (classifyingMap q hq U y₀ hy₀ h)
        = eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ h.left
          ≫ eqToHom (classifyingHobj q hq U y₀ hy₀ W').symm ∧
      classifyingMap q hq U y₀ hy₀ h ≫ classifyingStr q hq U y₀ hy₀ W'
        = classifyingStr q hq U y₀ hy₀ W :=
  (hq.unique_lift (classifyingStr q hq U y₀ hy₀ W') (classifyingStr q hq U y₀ hy₀ W)
    (eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ h.left
      ≫ eqToHom (classifyingHobj q hq U y₀ hy₀ W').symm)
    (map_cond q hq U y₀ hy₀ h)).exists.choose_spec

/-- The functorial action of the classifying construction lies over `h.left`: `q` sends
`classifyingMap … h` to `h.left`, conjugated by `eqToHom`s. First half of the `unique_lift`
specification that defines `classifyingMap`, and what makes `classifyingFunctor ⋙ q` equal to
`Over.forget U`. -/
theorem classifyingMap_map (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' : Over U} (h : W ⟶ W') :
    q.map (classifyingMap q hq U y₀ hy₀ h)
      = eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ h.left
        ≫ eqToHom (classifyingHobj q hq U y₀ hy₀ W').symm :=
  (classifyingMap_spec q hq U y₀ hy₀ h).1

/-- The chosen pullbacks are compatible with the structural morphisms: `classifyingMap … h`
followed by the structural morphism of `W'` is the structural morphism of `W`. Second half of the
`unique_lift` specification defining `classifyingMap`. -/
theorem classifyingMap_comp_str (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' : Over U} (h : W ⟶ W') :
    classifyingMap q hq U y₀ hy₀ h ≫ classifyingStr q hq U y₀ hy₀ W'
      = classifyingStr q hq U y₀ hy₀ W :=
  (classifyingMap_spec q hq U y₀ hy₀ h).2

/-- `classifyingMap … h` is the *only* morphism over `h.left` compatible with the structural
morphisms. Uniqueness is what makes the construction functorial: `classifyingMap_id` and
`classifyingMap_comp` are proved by checking that `𝟙` and a composite meet this specification. -/
theorem classifyingMap_unique (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' : Over U} (h : W ⟶ W')
    (χ : classifyingObj q hq U y₀ hy₀ W ⟶ classifyingObj q hq U y₀ hy₀ W')
    (hmap : q.map χ = eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ h.left
        ≫ eqToHom (classifyingHobj q hq U y₀ hy₀ W').symm)
    (hcomp : χ ≫ classifyingStr q hq U y₀ hy₀ W' = classifyingStr q hq U y₀ hy₀ W) :
    χ = classifyingMap q hq U y₀ hy₀ h :=
  (hq.unique_lift (classifyingStr q hq U y₀ hy₀ W') (classifyingStr q hq U y₀ hy₀ W)
    (eqToHom (classifyingHobj q hq U y₀ hy₀ W) ≫ h.left
      ≫ eqToHom (classifyingHobj q hq U y₀ hy₀ W').symm)
    (map_cond q hq U y₀ hy₀ h)).unique ⟨hmap, hcomp⟩
    (classifyingMap_spec q hq U y₀ hy₀ h)

/-- The identity of `W` acts as the identity on the chosen pullback, because `𝟙` itself satisfies
the specification of `classifyingMap_unique`. The `map_id` field of `classifyingFunctor`. -/
theorem classifyingMap_id (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) (W : Over U) :
    classifyingMap q hq U y₀ hy₀ (𝟙 W) = 𝟙 (classifyingObj q hq U y₀ hy₀ W) := by
  symm
  apply classifyingMap_unique
  · simp
  · simp

/-- The action on a composite `h ≫ h'` is the composite of the actions, since that composite lies
over `h.left ≫ h'.left` and is compatible with the structural morphisms, hence is the morphism
characterised by `classifyingMap_unique`. The `map_comp` field of `classifyingFunctor`. -/
theorem classifyingMap_comp (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' W'' : Over U} (h : W ⟶ W') (h' : W' ⟶ W'') :
    classifyingMap q hq U y₀ hy₀ (h ≫ h')
      = classifyingMap q hq U y₀ hy₀ h ≫ classifyingMap q hq U y₀ hy₀ h' := by
  symm
  apply classifyingMap_unique
  · rw [Functor.map_comp, classifyingMap_map, classifyingMap_map]
    have hl : (h ≫ h').left = h.left ≫ h'.left := rfl
    rw [hl]
    simp
  · rw [Category.assoc, classifyingMap_comp_str, classifyingMap_comp_str]

/-- The classifying functor `G : Over U ⥤ 𝒴`. -/
@[implicit_reducible]
noncomputable def classifyingFunctor (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) : Over U ⥤ 𝒴 where
  obj W := classifyingObj q hq U y₀ hy₀ W
  map h := classifyingMap q hq U y₀ hy₀ h
  map_id W := classifyingMap_id q hq U y₀ hy₀ W
  map_comp h h' := classifyingMap_comp q hq U y₀ hy₀ h h'

/-- The classifying functor `classifyingFunctor q hq U y₀ hy₀` sends a morphism `h` of `Over U`
to `classifyingMap q hq U y₀ hy₀ h`. -/
@[simp]
lemma classifyingFunctor_map (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) {W W' : Over U} (h : W ⟶ W') :
    (classifyingFunctor q hq U y₀ hy₀).map h = classifyingMap q hq U y₀ hy₀ h := rfl

/-- Factorisation in a groupoid fibration: two morphisms `m1, m2` into a common target,
both lying over the same `g`, are connected by a unique vertical morphism. -/
theorem factor (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    {U V : 𝒞} (g : V ⟶ U) {s1 s2 t : 𝒴} (m1 : s1 ⟶ t) (m2 : s2 ⟶ t)
    (hm1 : q.IsHomLift g m1) (hm2 : q.IsHomLift g m2) :
    ∃! χ : s1 ⟶ s2, q.map χ = eqToHom (CategoryTheory.IsHomLift.domain_eq q g m1)
        ≫ eqToHom (CategoryTheory.IsHomLift.domain_eq q g m2).symm ∧ χ ≫ m2 = m1 := by
  have hs1 := CategoryTheory.IsHomLift.domain_eq q g m1
  have hs2 := CategoryTheory.IsHomLift.domain_eq q g m2
  set f : q.obj s1 ⟶ q.obj s2 := eqToHom hs1 ≫ eqToHom hs2.symm with hfdef
  apply hq.unique_lift m2 m1 f
  rw [hfdef, CategoryTheory.IsHomLift.fac' q g m1, CategoryTheory.IsHomLift.fac' q g m2]; simp

/-- The vertical isomorphism produced by `factor`. -/
noncomputable def vertIso (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    {U V : 𝒞} (g : V ⟶ U) {s1 s2 t : 𝒴} (m1 : s1 ⟶ t) (m2 : s2 ⟶ t)
    (hm1 : q.IsHomLift g m1) (hm2 : q.IsHomLift g m2) : s1 ≅ s2 :=
  let χ := (factor q hq g m1 m2 hm1 hm2).exists.choose
  let χ' := (factor q hq g m2 m1 hm2 hm1).exists.choose
  { hom := χ
    inv := χ'
    hom_inv_id := by
      obtain ⟨hχmap, hχfac⟩ := (factor q hq g m1 m2 hm1 hm2).exists.choose_spec
      obtain ⟨hχ'map, hχ'fac⟩ := (factor q hq g m2 m1 hm2 hm1).exists.choose_spec
      obtain ⟨_, _, huniq⟩ := factor q hq g m1 m1 hm1 hm1
      rw [huniq (χ ≫ χ') ⟨by rw [Functor.map_comp, hχmap, hχ'map]; simp,
                          by rw [Category.assoc, hχ'fac, hχfac]⟩, huniq (𝟙 s1) ⟨by simp, by simp⟩]
    inv_hom_id := by
      obtain ⟨hχmap, hχfac⟩ := (factor q hq g m1 m2 hm1 hm2).exists.choose_spec
      obtain ⟨hχ'map, hχ'fac⟩ := (factor q hq g m2 m1 hm2 hm1).exists.choose_spec
      obtain ⟨_, _, huniq⟩ := factor q hq g m2 m2 hm2 hm2
      rw [huniq (χ' ≫ χ) ⟨by rw [Functor.map_comp, hχ'map, hχmap]; simp,
                          by rw [Category.assoc, hχfac, hχ'fac]⟩, huniq (𝟙 s2) ⟨by simp, by simp⟩] }

/-- `vertIso … m1 m2` factors `m1` through `m2`: its forward component composed with `m2` is `m1`.
This is the triangle that identifies the pullback objects of `m1` and `m2` compatibly, and it is
what supplies the coherence `w` field of the categorical-pullback morphisms in the main proof. -/
theorem vertIso_comp (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    {U V : 𝒞} (g : V ⟶ U) {s1 s2 t : 𝒴} (m1 : s1 ⟶ t) (m2 : s2 ⟶ t)
    (hm1 : q.IsHomLift g m1) (hm2 : q.IsHomLift g m2) :
    (vertIso q hq g m1 m2 hm1 hm2).hom ≫ m2 = m1 :=
  have hspec := (factor q hq g m1 m2 hm1 hm2).exists.choose_spec
  hspec.2

/-- `vertIso … m1 m2` is *vertical*: its forward component lies over `𝟙 V`, because `factor`
produces it over the `eqToHom` identifying the two domains, and both domains sit over `V`. -/
theorem vertIso_isHomLift (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    {U V : 𝒞} (g : V ⟶ U) {s1 s2 t : 𝒴} (m1 : s1 ⟶ t) (m2 : s2 ⟶ t)
    (hm1 : q.IsHomLift g m1) (hm2 : q.IsHomLift g m2) :
    q.IsHomLift (𝟙 V) (vertIso q hq g m1 m2 hm1 hm2).hom := by
  have hspec := (factor q hq g m1 m2 hm1 hm2).exists.choose_spec
  refine CategoryTheory.IsHomLift.of_fac' q (𝟙 V) _
    (CategoryTheory.IsHomLift.domain_eq q g m1) (CategoryTheory.IsHomLift.domain_eq q g m2) ?_
  rw [show (vertIso q hq g m1 m2 hm1 hm2).hom
      = (factor q hq g m1 m2 hm1 hm2).exists.choose from rfl,
      hspec.1]; simp

/-- **2-Yoneda (Stacks 02Y4/04SS).** Given a groupoid fibration `q` and an object `y₀` over
`U`, there is a 1-morphism `G : Over U ⥤ 𝒴` over `𝒞` together with a vertical iso
`G.obj (Over.mk (𝟙 U)) ≅ y₀`: the "object over `U` ⇒ classifying functor" construction,
where `G` sends `(T ⟶ U)` to a cartesian pullback of `y₀`. -/
theorem exists_classifying_functor (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (U : 𝒞) (y₀ : 𝒴) (hy₀ : q.obj y₀ = U) :
    ∃ (G : Over U ⥤ 𝒴) (_ : G ⋙ q = Over.forget U)
      (ξ : G.obj (Over.mk (𝟙 U)) ≅ y₀), q.IsHomLift (𝟙 U) ξ.hom := by
  refine ⟨classifyingFunctor q hq U y₀ hy₀, ?_, ?_⟩
  · -- G ⋙ q = Over.forget U
    refine CategoryTheory.Functor.ext (fun W => classifyingHobj q hq U y₀ hy₀ W) ?_
    intro W W' h
    rw [Functor.comp_map, classifyingFunctor_map, classifyingMap_map]
    rfl
  · -- the vertical iso at Over.mk (𝟙 U)
    set W₀ : Over U := Over.mk (𝟙 U) with hW₀
    have hW₀hom : W₀.hom = 𝟙 U := rfl
    have hstr : q.IsHomLift (𝟙 U) (classifyingStr q hq U y₀ hy₀ W₀) := by
      have := classifyingStr_isHomLift q hq U y₀ hy₀ W₀
      rwa [hW₀hom] at this
    have hid : q.IsHomLift (𝟙 U) (𝟙 y₀) :=
      CategoryTheory.IsHomLift.of_fac' q (𝟙 U) (𝟙 y₀) hy₀ hy₀ (by simp)
    refine ⟨vertIso q hq (𝟙 U) (classifyingStr q hq U y₀ hy₀ W₀) (𝟙 y₀) hstr hid, ?_⟩
    exact vertIso_isHomLift q hq (𝟙 U) (classifyingStr q hq U y₀ hy₀ W₀) (𝟙 y₀) hstr hid

end ClassifyingFunctor

/-- **The Stacks 02Y3 bridge.** A representable category fibred in groupoids is fibred in setoids.
Lifts and their uniqueness transfer to `s` from `Over.forget X`, which is fibred in groupoids,
along the equivalence `E` over `𝒟`; and each fibre `s.Fiber V` is thin because a morphism of
`(Over X).Fiber V` is already pinned by the triangle it commutes over `V`. -/
theorem isFiberedInSetoids_of_isRepresentableCFG
    {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟] (s : 𝒮 ⥤ 𝒟)
    (hs : IsRepresentableCFG s) : s.IsFiberedInSetoids := by
  -- Unpack the slice `Over X` and the equivalence `E : 𝒮 ⥤ Over X` over `𝒟`.
  obtain ⟨X, E, hE⟩ := hs
  have hcomm : E ⋙ Over.forget X = s := hE.isCartesianFunctor.comm
  -- `E` is an equivalence of categories (so fully faithful), and we have a quasi-inverse
  -- `G` together with unit/counit natural isos that are over the base `𝒟`.
  have hEequiv : E.IsEquivalence :=
    SliceEquivalence.isEquivalence_of_isEquivalenceOver s X E hE
  obtain ⟨G, hGcart, ⟨η, hη⟩, ⟨ε, hε⟩⟩ := hE.exists_inverse
  -- `Over.forget X` is fibred in groupoids: the groupoid half of Stacks 02Y3 for the slice.
  have hfgU : (Over.forget X).IsFiberedInGroupoids :=
    (StacksRepresentableCFG.over_isFiberedInSetoids X).isFiberedInGroupoids
  refine { isFiberedInGroupoids := { exists_lift := ?_, unique_lift := ?_ }, fiber_isThin := ?_ }
  · -- Transfer existence of lifts from `Over.forget X` to `s` along `E`.
    intro V U f a ha
    have hEa : (Over.forget X).obj (E.obj a) = U := by rw [← hcomm] at ha; exact ha
    obtain ⟨y', φ', hφ'⟩ := hfgU.exists_lift f (E.obj a) hEa
    exact ⟨G.obj y', G.map φ' ≫ ε.hom.app a,
      SliceEquivalence.bridge s X E hcomm f _
        (SliceEquivalence.core_lift s X E hcomm G η hη ε hε f a y' φ' hφ')⟩
  · exact fun φ ψ f hf => SliceEquivalence.s_unique_lift s X E hcomm hfgU φ ψ f hf
  · -- `fiber_isThin`: the fibre categories of `s` are thin.
    exact fun _ _ _ => ⟨fun f g => SliceEquivalence.s_fibers_setoid s X E hcomm f g⟩

/-- **The comparison step.** Given a classifying 1-morphism `G : 𝒞/U ⥤ 𝒴` over `𝒞` together with
a vertical isomorphism `ξ : G(𝟙_U) ≅ F(x')`, two parallel morphisms `φ, φ' : x ⟶ x'` of `𝒳` with
`F.map φ = F.map φ'` assemble into two morphisms `Φ, Φ'` of the 2-fibre product `(𝒞/U) ×_𝒴 𝒳`
sharing their `𝒞/U`-component `β`. So `π₁.map Φ = π₁.map Φ'`, and if `π₁` is fibred in setoids
then `Φ = Φ'` (Stacks 02Y4); reading off the `𝒳`-component gives `φ = φ'`.

This is steps 3–5 of the argument for Stacks 02Y8; the hypothesis on `π₁` is what representability
of `F` supplies, through `isFiberedInSetoids_of_isRepresentableCFG`. -/
theorem fiberHom_injective_of_fst_isFiberedInSetoids
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids) (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p)
    (U : 𝒞) (G : Over U ⥤ 𝒴) (hGq : G ⋙ q = Over.forget U)
    (hsetoid : (TwoFibreProductOver.fst (Over.forget U) p q G F).IsFiberedInSetoids)
    {x x' : 𝒳} (hxU : p.obj x = U) (hx'U : p.obj x' = U)
    (ξ : G.obj (Over.mk (𝟙 U)) ≅ F.obj x') (hξ : q.IsHomLift (𝟙 U) ξ.hom)
    (φ φ' : x ⟶ x') (hφ : F.map φ = F.map φ') : φ = φ' := by
  set g : U ⟶ U := eqToHom hxU.symm ≫ p.map φ ≫ eqToHom hx'U with hg
  -- `φ` and `φ'` lie over the same `g`, because they have the same image under `F` and `F` is a
  -- 1-morphism over `𝒞`; hence so do `F.map φ` and, through `hGq`, the base morphism `β`.
  have hpmap : p.map φ' = p.map φ := by
    rw [Functor.congr_hom hF.symm φ, Functor.congr_hom hF.symm φ']
    simp [Functor.comp_map, hφ]
  have hlift_φ : p.IsHomLift g φ := IsHomLift.of_fac' p g φ hxU hx'U (by simp [hg])
  have hlift_φ' : p.IsHomLift g φ' := IsHomLift.of_fac' p g φ' hxU hx'U (by simp [hg, hpmap])
  have hlift_Fφ : q.IsHomLift g (F.map φ) := Functor.isHomLift_map_of_comp_eq hF g φ
  set β : Over.mk g ⟶ Over.mk (𝟙 U) := Over.homMk g (by simp) with hβ
  have hlift_β : (Over.forget U).IsHomLift g β :=
    IsHomLift.of_fac' (Over.forget U) g β rfl rfl (by simp [hβ])
  have hlift_Gβ : q.IsHomLift g (G.map β) := Functor.isHomLift_map_of_comp_eq hGq g β
  have hlift_m₁ : q.IsHomLift g (G.map β ≫ ξ.hom) :=
    IsHomLift.comp_lift_id_right q g (G.map β) ξ.hom
  -- The vertical comparison isomorphism `G(g) ≅ F(x)` factoring `G β ≫ ξ` through `F φ`.
  set Piso : G.obj (Over.mk g) ≅ F.obj x :=
    ClassifyingFunctor.vertIso q hq g (G.map β ≫ ξ.hom) (F.map φ) hlift_m₁ hlift_Fφ with hPiso
  have hPisocomp : Piso.hom ≫ F.map φ = G.map β ≫ ξ.hom :=
    ClassifyingFunctor.vertIso_comp q hq g (G.map β ≫ ξ.hom) (F.map φ) hlift_m₁ hlift_Fφ
  -- The two objects of the 2-fibre product over `𝒞`: both lie over the base object `U`, and both
  -- comparison isomorphisms are vertical, which is what that product requires.
  set P : TwoFibreProductOver (Over.forget U) p q G F :=
    { base := U, x := Over.mk g, y := x, hx := rfl, hy := hxU, iso := Piso
      vertical := ClassifyingFunctor.vertIso_isHomLift q hq g (G.map β ≫ ξ.hom) (F.map φ)
        hlift_m₁ hlift_Fφ } with hP
  set Q : TwoFibreProductOver (Over.forget U) p q G F :=
    { base := U, x := Over.mk (𝟙 U), y := x', hx := rfl, hy := hx'U, iso := ξ
      vertical := hξ } with hQ
  -- The two parallel morphisms with common `𝒞/U`-component `β`; the coherence square is the flip
  -- of `hPisocomp`, and for `Φ'` it is the same one after `hφ`.
  set Φ : P ⟶ Q :=
    { hbase := g, a := β, b := φ, ha := hlift_β, hb := hlift_φ, w := hPisocomp.symm } with hΦ
  set Φ' : P ⟶ Q :=
    { hbase := g, a := β, b := φ', ha := hlift_β, hb := hlift_φ'
      w := hφ ▸ hPisocomp.symm } with hΦ'
  exact congrArg TwoFibreProductOver.Hom.b
    (ClassifyingFunctor.map_injective_of_isFiberedInSetoids
      (TwoFibreProductOver.fst (Over.forget U) p q G F) Φ Φ' rfl)

/-- **Injectivity of `F` on fibre morphisms (the representability step).** Under the groupoid and
representability hypotheses, `F` is injective on morphisms of `𝒳` lying over `𝟙 U`: parallel
`φ, φ'` with `F.map φ = F.map φ'` are equal.

Following Stacks 02Y5: by 2-Yoneda (`ClassifyingFunctor.exists_classifying_functor`) there is a
1-morphism `G : 𝒞/U ⥤ 𝒴` over `𝒞` with a vertical isomorphism `G(𝟙_U) ≅ F(x')` (step 1);
representability of `F` at `G` makes the projection `(𝒞/U) ×_𝒴 𝒳 ⥤ 𝒞/U` a representable category
fibred in groupoids, hence fibred in setoids by `isFiberedInSetoids_of_isRepresentableCFG`
(step 2); and `fiberHom_injective_of_fst_isFiberedInSetoids` reads `φ = φ'` off that thinness
(steps 3–5). -/
theorem fiberHom_injective_of_isRepresentableMorphism
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞)
    (hq : q.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p)
    (hrep : IsRepresentableMorphism p q F) (U : 𝒞)
    {a b : p.Fiber U}
    (φ φ' : Fiber.fiberInclusion.obj a ⟶ Fiber.fiberInclusion.obj b)
    (hφ : F.map φ = F.map φ') : φ = φ' := by
  obtain ⟨G, hGq, ξ, hξ⟩ :=
    ClassifyingFunctor.exists_classifying_functor q hq U (F.obj (Fiber.fiberInclusion.obj b))
      ((Functor.congr_obj hF (Fiber.fiberInclusion.obj b)).trans b.2)
  exact fiberHom_injective_of_fst_isFiberedInSetoids p q hq F hF U G hGq
    (isFiberedInSetoids_of_isRepresentableCFG _ (hrep U G hGq)) a.2 b.2 ξ hξ φ φ' hφ

/-- **Stacks 02Y8** (Lemma 4.42.4), the stated implication. If `F : 𝒳 ⥤ 𝒴` is a representable
1-morphism over `𝒞` between categories fibred in groupoids, then for every object `U` of `𝒞` the
induced functor on fibre categories `F_U : 𝒳_U ⥤ 𝒴_U` is faithful. The converse is not proved
here. -/
@[stacks 02Y8]
theorem inducedFiberFunctor_faithful_of_isRepresentableMorphism
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞)
    (hq : q.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p)
    (hrep : IsRepresentableMorphism p q F) (U : 𝒞) :
    (inducedFiberFunctor p q F hF U).Faithful := by
  -- By the formal reduction above it suffices to prove that `F` is injective on
  -- morphisms of `𝒳` lying over `𝟙 U`; that is the content of
  -- `fiberHom_injective_of_isRepresentableMorphism` (the representability step).
  refine inducedFiberFunctor_faithful_of_fiberHom_injective p q F hF U ?_
  intro a b φ φ' hφ
  exact fiberHom_injective_of_isRepresentableMorphism p q hq F hF hrep U φ φ' hφ

end Stacks.RepresentableMorphism
