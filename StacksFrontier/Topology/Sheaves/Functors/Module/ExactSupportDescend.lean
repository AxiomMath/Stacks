module

public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupport

/-!
# The descended action on sections annihilated by the kernel ideal

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces with kernel ideal
`ℐ = ker(𝒪_X ⟶ i_* 𝒪_Z)`, and let `s` be a section of an `𝒪_X`-module `F` over an open `W ⊆ X`
which is annihilated sheaf-locally by `ℐ`.  Then the `𝒪_X`-action on `s` descends to an
`i_* 𝒪_Z`-action: for every open `V ⊆ W` and every `b ∈ (i_* 𝒪_Z)(V)` there is a unique section
`b · s|_V` of `F` over `V` which agrees with `a · s|_{V'}` whenever `a ∈ 𝒪_X(V')` is a local lift
of `b` along the comorphism.

## Main definitions

* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.IsDescendedSmul` is the
  predicate characterising `b · s|_V` by its behaviour against every local lift of `b`.
* `ClosedQuotientMorphismOfRingedSpaces.descendedSmul` is the section `b · s|_V` itself.

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.exists_isDescendedSmul` and
  `ClosedQuotientMorphismOfRingedSpaces.isDescendedSmul_unique`: existence and uniqueness of
  `b · s|_V`.
* `ClosedQuotientMorphismOfRingedSpaces.descendedSmul_add`,
  `ClosedQuotientMorphismOfRingedSpaces.descendedSmul_pushedRingHom_mul`,
  `ClosedQuotientMorphismOfRingedSpaces.descendedSmul_restrict` and
  `ClosedQuotientMorphismOfRingedSpaces.descendedSmul_one`: the action is additive, semilinear
  over `𝒪_X`, compatible with restriction, and recovers `s` at `b = 1`.
* `ClosedQuotientMorphismOfRingedSpaces.exists_mem_sections_restrict_eq`: an annihilated section
  over `U` extends to an annihilated section over the largest open `i_! i⁻¹ U` with the same
  inverse image, by zero off `U`.

## Implementation notes

Existence of `b · s|_V` is a gluing: the local lifts of `b` form an index type `LocalLift`, the
sections `a · s` attached to them agree on overlaps because the difference of two lifts lies in
`ℐ`, and `F` is a sheaf.  This is the only place where
`ClosedQuotientMorphismOfRingedSpaces.isLocallySurjective` is used, and it is used exactly to
produce those lifts.

Uniqueness makes all the algebraic properties cheap: each one is proved by checking the defining
property of `IsDescendedSmul` for the candidate section, and `isDescendedSmul_of_locally` reduces
that check to a neighbourhood of each point.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open TopologicalSpace.Opens

universe u

namespace RingedSpaceModuleAdjunction

namespace ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The comorphism, the kernel ideal, and local lifts -/

/-- Membership in the kernel ideal, phrased through the comorphism `𝒪_X ⟶ i_* 𝒪_Z` in the shape
`pushedRingHom` that the internal Hom consumes. -/
lemma mem_kernelIdeal_iff_pushedRingHom_eq_zero (U : Opens S.X)
    (a : (structureSheafRing S.X).obj.obj (op U)) :
    a ∈ S.kernelIdeal U ↔ S.pushedRingHom.hom.app (op U) a = 0 :=
  Iff.rfl

/-- The comorphism commutes with restriction maps. -/
lemma pushedRingHom_naturality {A B : Opens S.X} (h : B ≤ A)
    (x : (structureSheafRing S.X).obj.obj (op A)) :
    S.pushedRingHom.hom.app (op B) ((structureSheafRing S.X).obj.map (homOfLE h).op x) =
      S.pushedRingSheaf.obj.map (homOfLE h).op (S.pushedRingHom.hom.app (op A) x) :=
  NatTrans.naturality_apply S.pushedRingHom.hom (homOfLE h).op x

/-- Two successive restrictions in `i_* 𝒪_Z` compose to the restriction between the end
points. -/
lemma pushedRingSheaf_map_map {A B C : Opens S.X} (hBA : B ≤ A) (hCB : C ≤ B) (hCA : C ≤ A)
    (x : S.pushedRingSheaf.obj.obj (op A)) :
    S.pushedRingSheaf.obj.map (homOfLE hCB).op (S.pushedRingSheaf.obj.map (homOfLE hBA).op x) =
      S.pushedRingSheaf.obj.map (homOfLE hCA).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Two successive restrictions in a presheaf of modules on a space compose to the restriction
between the end points. -/
lemma map_map_of_hom {T : TopCat.{u}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)
    {A B C : Opens T} (f : B ⟶ A) (g : C ⟶ B) (hCA : C ≤ A) (t : M.obj (op A)) :
    M.map g.op (M.map f.op t) = M.map (homOfLE hCA).op t := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- `map_map_of_hom` for the inclusions named by their inequalities. -/
lemma map_map_of_le {T : TopCat.{u}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)
    {A B C : Opens T} (hBA : B ≤ A) (hCB : C ≤ B) (hCA : C ≤ A) (t : M.obj (op A)) :
    M.map (homOfLE hCB).op (M.map (homOfLE hBA).op t) = M.map (homOfLE hCA).op t :=
  map_map_of_hom M (homOfLE hBA) (homOfLE hCB) hCA t

/-- **Local surjectivity of the comorphism.** Every section of `i_* 𝒪_Z` over `U` lifts to a
section of `𝒪_X` on some neighbourhood, inside `U`, of any prescribed point of `U`. -/
lemma exists_lift_of_mem (U : Opens S.X) (b : S.pushedRingSheaf.obj.obj (op U))
    {x : S.X.carrier} (hx : x ∈ U) :
    ∃ (V : Opens S.X) (hVU : V ≤ U), x ∈ V ∧ ∃ a : (structureSheafRing S.X).obj.obj (op V),
      S.pushedRingHom.hom.app (op V) a = S.pushedRingSheaf.obj.map (homOfLE hVU).op b := by
  obtain ⟨V, hVU, ⟨a, ha⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).1 S.isLocallySurjective U b x hx
  exact ⟨V, hVU, hxV, a, ha⟩

/-- An open subset disjoint from the image of `Z` has empty preimage. -/
private lemma opensMap_eq_bot_of_le_opensComplRange {B : Opens S.X}
    (hB : B ≤ S.opensComplRange) : (opensMap S.i).obj B = ⊥ := by
  refine le_bot_iff.1 ?_
  rw [← S.opensMap_opensComplRange]
  exact fun z hz => hB hz

/-- Off the image of `Z` the comorphism lands in the zero ring, so the kernel ideal is the unit
ideal there. -/
lemma one_mem_kernelIdeal_of_le_opensComplRange {B : Opens S.X} (hB : B ≤ S.opensComplRange) :
    (1 : (structureSheafRing S.X).obj.obj (op B)) ∈ S.kernelIdeal B :=
  (S.subsingleton_pushedRingSheaf_obj B (S.opensMap_eq_bot_of_le_opensComplRange hB)).elim _ _

/-- Off the image of `Z` the sheaf `i_* 𝒪_Z` vanishes. -/
lemma pushedRingSheaf_eq_zero_of_le_opensComplRange {B : Opens S.X}
    (hB : B ≤ S.opensComplRange) (b : S.pushedRingSheaf.obj.obj (op B)) : b = 0 :=
  (S.subsingleton_pushedRingSheaf_obj B (S.opensMap_eq_bot_of_le_opensComplRange hB)).elim _ _

/-- Restricting a local lift of `b` gives a local lift of `b` on the smaller open. -/
private lemma pushedRingHom_map_eq {V V' B : Opens S.X} {h : V' ≤ V} (hB : B ≤ V') (hBV : B ≤ V)
    {b : S.pushedRingSheaf.obj.obj (op V)} {a : (structureSheafRing S.X).obj.obj (op V')}
    (ha : S.pushedRingHom.hom.app (op V') a = S.pushedRingSheaf.obj.map (homOfLE h).op b) :
    S.pushedRingHom.hom.app (op B) ((structureSheafRing S.X).obj.map (homOfLE hB).op a) =
      S.pushedRingSheaf.obj.map (homOfLE hBV).op b := by
  rw [S.pushedRingHom_naturality hB, ha, S.pushedRingSheaf_map_map h hB hBV]

/-- The difference of two local lifts of one section of `i_* 𝒪_Z` lies in the kernel ideal on the
overlap. -/
lemma sub_mem_kernelIdeal_of_lift_eq {V V₁ V₂ : Opens S.X} {h₁ : V₁ ≤ V} {h₂ : V₂ ≤ V}
    {b : S.pushedRingSheaf.obj.obj (op V)}
    {a₁ : (structureSheafRing S.X).obj.obj (op V₁)} {a₂ : (structureSheafRing S.X).obj.obj (op V₂)}
    (ha₁ : S.pushedRingHom.hom.app (op V₁) a₁ = S.pushedRingSheaf.obj.map (homOfLE h₁).op b)
    (ha₂ : S.pushedRingHom.hom.app (op V₂) a₂ = S.pushedRingSheaf.obj.map (homOfLE h₂).op b)
    {B : Opens S.X} (hB₁ : B ≤ V₁) (hB₂ : B ≤ V₂) :
    (structureSheafRing S.X).obj.map (homOfLE hB₁).op a₁ -
        (structureSheafRing S.X).obj.map (homOfLE hB₂).op a₂ ∈ S.kernelIdeal B := by
  rw [S.mem_kernelIdeal_iff_pushedRingHom_eq_zero, map_sub,
    S.pushedRingHom_map_eq hB₁ (hB₁.trans h₁) ha₁, S.pushedRingHom_map_eq hB₂ (hB₂.trans h₂) ha₂,
    sub_self]

/-- The local lifts of a section `b` of `i_* 𝒪_Z` over `V` along the comorphism: an open subset
of `V` together with a section of `𝒪_X` on it mapping to the restriction of `b`. -/
structure LocalLift {V : Opens S.X} (b : S.pushedRingSheaf.obj.obj (op V)) where
  /-- The open subset of `V` on which the lift is defined. -/
  carrier : Opens S.X
  /-- The lift is defined on an open subset of `V`. -/
  le : carrier ≤ V
  /-- The lifted section of the structure sheaf. -/
  elem : (structureSheafRing S.X).obj.obj (op carrier)
  /-- The lifted section maps to the restriction of `b`. -/
  spec : S.pushedRingHom.hom.app (op carrier) elem =
    S.pushedRingSheaf.obj.map (homOfLE le).op b

/-! ### The descended action -/

variable (F : SheafOfModules.{u} (structureSheafRing S.X))

/-- Restricting a section of the structure sheaf acting on a restricted section of `F`. -/
lemma map_smul_map {A B C : Opens S.X} (hBA : B ≤ A) (hCB : C ≤ B) (hCA : C ≤ A)
    (a : (structureSheafRing S.X).obj.obj (op B)) (t : F.val.obj (op A)) :
    F.val.map (homOfLE hCB).op (a • F.val.map (homOfLE hBA).op t) =
      (structureSheafRing S.X).obj.map (homOfLE hCB).op a • F.val.map (homOfLE hCA).op t := by
  have h := PresheafOfModules.map_smul F.val (homOfLE hCB).op a (F.val.map (homOfLE hBA).op t)
  rw [map_map_of_le F.val hBA hCB hCA] at h
  exact h

/-- A scalar acting on a vanishing restricted section vanishes. -/
lemma smul_map_eq_zero_of_map_eq_zero {A B : Opens S.X} (hBA : B ≤ A)
    (a : (structureSheafRing S.X).obj.obj (op B)) (t : F.val.obj (op A))
    (ht : F.val.map (homOfLE hBA).op t = 0) : a • F.val.map (homOfLE hBA).op t = 0 :=
  (congrArg (a • ·) ht).trans (smul_zero a)

/-- Two sections of a sheaf of modules which agree near every point of their common domain are
equal. -/
lemma eq_of_locally_eq_of_mem (V : Opens S.X) (t t' : F.val.obj (op V))
    (h : ∀ x ∈ V, ∃ (V' : Opens S.X) (hle : V' ≤ V), x ∈ V' ∧
      F.val.map (homOfLE hle).op t = F.val.map (homOfLE hle).op t') : t = t' := by
  choose! V' hle hx heq using h
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨F.val.presheaf, F.isSheaf⟩ : TopCat.Sheaf _ _)
    (fun x : {x : S.X.carrier // x ∈ V} => V' x.1) V (fun x => homOfLE (hle x.1 x.2))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx x hx'⟩) t t' fun x => heq x.1 x.2

/-- Unique gluing in a sheaf of modules, in terms of sections over open subsets and the
restriction maps `PresheafOfModules.map`. -/
lemma exists_gluing {ι : Type*} (Wf : ι → Opens S.X) (V : Opens S.X) (hle : ∀ i, Wf i ≤ V)
    (hcov : V ≤ iSup Wf) (sf : ∀ i, F.val.obj (op (Wf i)))
    (hsf : ∀ i j, F.val.map (homOfLE (inf_le_left : Wf i ⊓ Wf j ≤ Wf i)).op (sf i) =
      F.val.map (homOfLE (inf_le_right : Wf i ⊓ Wf j ≤ Wf j)).op (sf j)) :
    ∃ t : F.val.obj (op V), ∀ i, F.val.map (homOfLE (hle i)).op t = sf i := by
  have hcompat : TopCat.Presheaf.IsCompatible F.val.presheaf Wf sf := fun i j => hsf i j
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨F.val.presheaf, F.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} S.X.carrier) Wf V
    (fun i => homOfLE (hle i)) hcov sf hcompat
  exact ⟨t, ht⟩

variable {W : Opens S.X} (s : F.val.obj (op W))
  (hs : s ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F W)

include hs in
/-- Two local lifts of one section of `i_* 𝒪_Z` act on an annihilated section in the same way on
the overlap of their domains. -/
lemma smul_restrict_eq_of_lift_eq {V V₁ V₂ : Opens S.X} {h₁ : V₁ ≤ V} {h₂ : V₂ ≤ V}
    {b : S.pushedRingSheaf.obj.obj (op V)}
    {a₁ : (structureSheafRing S.X).obj.obj (op V₁)} {a₂ : (structureSheafRing S.X).obj.obj (op V₂)}
    (ha₁ : S.pushedRingHom.hom.app (op V₁) a₁ = S.pushedRingSheaf.obj.map (homOfLE h₁).op b)
    (ha₂ : S.pushedRingHom.hom.app (op V₂) a₂ = S.pushedRingSheaf.obj.map (homOfLE h₂).op b)
    {B : Opens S.X} (hB₁ : B ≤ V₁) (hB₂ : B ≤ V₂) (hBW : B ≤ W) :
    (structureSheafRing S.X).obj.map (homOfLE hB₁).op a₁ • F.val.map (homOfLE hBW).op s =
      (structureSheafRing S.X).obj.map (homOfLE hB₂).op a₂ • F.val.map (homOfLE hBW).op s := by
  have h := hs B hBW _ (S.sub_mem_kernelIdeal_of_lift_eq ha₁ ha₂ hB₁ hB₂)
  rw [sub_smul, sub_eq_zero] at h
  exact h

/-- `t` is the result of acting on the annihilated section `s` by the section `b` of `i_* 𝒪_Z`:
every local lift `a` of `b` along the comorphism satisfies `t|_{V'} = a · s|_{V'}`. -/
def IsDescendedSmul {V : Opens S.X} (hVW : V ≤ W) (b : S.pushedRingSheaf.obj.obj (op V))
    (t : F.val.obj (op V)) : Prop :=
  ∀ (V' : Opens S.X) (hV'V : V' ≤ V) (a : (structureSheafRing S.X).obj.obj (op V')),
    S.pushedRingHom.hom.app (op V') a = S.pushedRingSheaf.obj.map (homOfLE hV'V).op b →
      F.val.map (homOfLE hV'V).op t = a • F.val.map (homOfLE (hV'V.trans hVW)).op s

/-- The descended action is determined by its defining property. -/
lemma isDescendedSmul_unique {V : Opens S.X} (hVW : V ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op V)) {t t' : F.val.obj (op V)}
    (ht : S.IsDescendedSmul F s hVW b t) (ht' : S.IsDescendedSmul F s hVW b t') : t = t' := by
  refine S.eq_of_locally_eq_of_mem F V t t' fun x hx => ?_
  obtain ⟨V', hV'V, hxV', a, ha⟩ := S.exists_lift_of_mem V b hx
  exact ⟨V', hV'V, hxV', (ht V' hV'V a ha).trans (ht' V' hV'V a ha).symm⟩

include hs in
/-- Checking the defining property of the descended action is a local matter. -/
lemma isDescendedSmul_of_locally {V : Opens S.X} (hVW : V ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op V)) (t : F.val.obj (op V))
    (h : ∀ x ∈ V, ∃ (V' : Opens S.X) (hV'V : V' ≤ V), x ∈ V' ∧
      ∃ a : (structureSheafRing S.X).obj.obj (op V'),
        S.pushedRingHom.hom.app (op V') a = S.pushedRingSheaf.obj.map (homOfLE hV'V).op b ∧
          F.val.map (homOfLE hV'V).op t = a • F.val.map (homOfLE (hV'V.trans hVW)).op s) :
    S.IsDescendedSmul F s hVW b t := by
  intro V₀ hV₀V a₀ ha₀
  refine S.eq_of_locally_eq_of_mem F V₀ _ _ fun x hx => ?_
  obtain ⟨V', hV'V, hxV', a, ha, hta⟩ := h x (hV₀V hx)
  refine ⟨V₀ ⊓ V', inf_le_left, ⟨hx, hxV'⟩, ?_⟩
  have hBV' : V₀ ⊓ V' ≤ V' := inf_le_right
  have hBV : V₀ ⊓ V' ≤ V := hBV'.trans hV'V
  have hBW : V₀ ⊓ V' ≤ W := hBV.trans hVW
  rw [map_map_of_le F.val hV₀V inf_le_left hBV,
    S.map_smul_map F (hV₀V.trans hVW) (inf_le_left : V₀ ⊓ V' ≤ V₀) hBW,
    ← map_map_of_le F.val hV'V hBV' hBV, hta, S.map_smul_map F (hV'V.trans hVW) hBV' hBW]
  exact S.smul_restrict_eq_of_lift_eq F s hs ha ha₀ hBV' inf_le_left hBW

include hs in
/-- **Existence of the descended action.** This is the only step that uses local surjectivity of
the comorphism: the sections `a · s` attached to the local lifts `a` of `b` agree on overlaps,
because two lifts differ by a section of the kernel ideal, and `F` is a sheaf. -/
lemma exists_isDescendedSmul {V : Opens S.X} (hVW : V ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op V)) : ∃ t, S.IsDescendedSmul F s hVW b t := by
  have hcover : V ≤ ⨆ l : S.LocalLift b, l.carrier := by
    intro x hx
    obtain ⟨V', hV'V, hxV', a, ha⟩ := S.exists_lift_of_mem V b hx
    exact Opens.mem_iSup.2 ⟨⟨V', hV'V, a, ha⟩, hxV'⟩
  have hcompat : ∀ l m : S.LocalLift b,
      F.val.map (homOfLE (inf_le_left : l.carrier ⊓ m.carrier ≤ l.carrier)).op
          (l.elem • F.val.map (homOfLE (l.le.trans hVW)).op s) =
        F.val.map (homOfLE (inf_le_right : l.carrier ⊓ m.carrier ≤ m.carrier)).op
          (m.elem • F.val.map (homOfLE (m.le.trans hVW)).op s) := by
    intro l m
    have hBW : l.carrier ⊓ m.carrier ≤ W := inf_le_left.trans (l.le.trans hVW)
    rw [S.map_smul_map F (l.le.trans hVW) inf_le_left hBW,
      S.map_smul_map F (m.le.trans hVW) inf_le_right hBW]
    exact S.smul_restrict_eq_of_lift_eq F s hs l.spec m.spec inf_le_left inf_le_right hBW
  obtain ⟨t, ht⟩ := S.exists_gluing F (fun l : S.LocalLift b => l.carrier) V (fun l => l.le)
    hcover (fun l => l.elem • F.val.map (homOfLE (l.le.trans hVW)).op s) hcompat
  exact ⟨t, fun V' hV'V a ha => ht ⟨V', hV'V, a, ha⟩⟩

/-- The action of a section `b` of `i_* 𝒪_Z` over `V ⊆ W` on an annihilated section `s` of `F`
over `W`: the unique section of `F` over `V` agreeing with `a · s` for every local lift `a` of
`b` along the comorphism. -/
noncomputable def descendedSmul {V : Opens S.X} (hVW : V ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op V)) : F.val.obj (op V) :=
  (S.exists_isDescendedSmul F s hs hVW b).choose

/-- `descendedSmul` has the defining property of the descended action. -/
lemma isDescendedSmul_descendedSmul {V : Opens S.X} (hVW : V ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op V)) :
    S.IsDescendedSmul F s hVW b (S.descendedSmul F s hs hVW b) :=
  (S.exists_isDescendedSmul F s hs hVW b).choose_spec

/-- Anything with the defining property of the descended action is `descendedSmul`. -/
lemma descendedSmul_eq {V : Opens S.X} (hVW : V ≤ W) (b : S.pushedRingSheaf.obj.obj (op V))
    {t : F.val.obj (op V)} (ht : S.IsDescendedSmul F s hVW b t) :
    S.descendedSmul F s hs hVW b = t :=
  S.isDescendedSmul_unique F s hVW b (S.isDescendedSmul_descendedSmul F s hs hVW b) ht

/-- The descended action is compatible with restriction to a smaller open subset. -/
lemma descendedSmul_restrict {V V' : Opens S.X} (hVW : V ≤ W) (hV'V : V' ≤ V)
    (b : S.pushedRingSheaf.obj.obj (op V)) :
    S.descendedSmul F s hs (hV'V.trans hVW) (S.pushedRingSheaf.obj.map (homOfLE hV'V).op b) =
      F.val.map (homOfLE hV'V).op (S.descendedSmul F s hs hVW b) := by
  refine S.descendedSmul_eq F s hs _ _ fun V₀ hV₀V' a ha => ?_
  have hV₀V : V₀ ≤ V := hV₀V'.trans hV'V
  rw [map_map_of_le F.val hV'V hV₀V' hV₀V]
  refine S.isDescendedSmul_descendedSmul F s hs hVW b V₀ hV₀V a ?_
  rw [ha, S.pushedRingSheaf_map_map hV'V hV₀V' hV₀V]

/-- The descended action of the zero section of `i_* 𝒪_Z` is zero. -/
lemma descendedSmul_zero {V : Opens S.X} (hVW : V ≤ W) :
    S.descendedSmul F s hs hVW 0 = 0 := by
  refine S.descendedSmul_eq F s hs hVW 0 fun V' hV'V a ha => ?_
  have hker : a ∈ S.kernelIdeal V' := by
    rw [S.mem_kernelIdeal_iff_pushedRingHom_eq_zero, ha, map_zero]
  exact (map_zero _).trans (hs V' (hV'V.trans hVW) a hker).symm

/-- The descended action is additive in the section of `i_* 𝒪_Z`. -/
lemma descendedSmul_add {V : Opens S.X} (hVW : V ≤ W)
    (b₁ b₂ : S.pushedRingSheaf.obj.obj (op V)) :
    S.descendedSmul F s hs hVW (b₁ + b₂) =
      S.descendedSmul F s hs hVW b₁ + S.descendedSmul F s hs hVW b₂ := by
  refine S.descendedSmul_eq F s hs hVW _
    (S.isDescendedSmul_of_locally F s hs hVW _ _ fun x hx => ?_)
  obtain ⟨V₁, h₁, hx₁, a₁, ha₁⟩ := S.exists_lift_of_mem V b₁ hx
  obtain ⟨V₂, h₂, hx₂, a₂, ha₂⟩ := S.exists_lift_of_mem V b₂ hx
  have hB₁ : V₁ ⊓ V₂ ≤ V₁ := inf_le_left
  have hB₂ : V₁ ⊓ V₂ ≤ V₂ := inf_le_right
  have hBV : V₁ ⊓ V₂ ≤ V := hB₁.trans h₁
  have hBW : V₁ ⊓ V₂ ≤ W := hBV.trans hVW
  refine ⟨V₁ ⊓ V₂, hBV, ⟨hx₁, hx₂⟩, (structureSheafRing S.X).obj.map (homOfLE hB₁).op a₁ +
    (structureSheafRing S.X).obj.map (homOfLE hB₂).op a₂, ?_, ?_⟩
  · rw [map_add, S.pushedRingHom_map_eq hB₁ hBV ha₁, S.pushedRingHom_map_eq hB₂ hBV ha₂,
      ← map_add]
  · have e₁ := S.isDescendedSmul_descendedSmul F s hs hVW b₁ (V₁ ⊓ V₂) hBV _
      (S.pushedRingHom_map_eq hB₁ hBV ha₁)
    have e₂ := S.isDescendedSmul_descendedSmul F s hs hVW b₂ (V₁ ⊓ V₂) hBV _
      (S.pushedRingHom_map_eq hB₂ hBV ha₂)
    rw [map_add, add_smul, e₁, e₂]
    rfl

/-- The descended action is semilinear over the structure sheaf: acting by `i^♯(r) · b` is acting
by `b` followed by multiplication by `r`. -/
lemma descendedSmul_pushedRingHom_mul {V : Opens S.X} (hVW : V ≤ W)
    (r : (structureSheafRing S.X).obj.obj (op V)) (b : S.pushedRingSheaf.obj.obj (op V)) :
    S.descendedSmul F s hs hVW (S.pushedRingHom.hom.app (op V) r * b) =
      r • S.descendedSmul F s hs hVW b := by
  refine S.descendedSmul_eq F s hs hVW _
    (S.isDescendedSmul_of_locally F s hs hVW _ _ fun x hx => ?_)
  obtain ⟨V', hV'V, hxV', a, ha⟩ := S.exists_lift_of_mem V b hx
  have hV'W : V' ≤ W := hV'V.trans hVW
  refine ⟨V', hV'V, hxV', (structureSheafRing S.X).obj.map (homOfLE hV'V).op r * a, ?_, ?_⟩
  · rw [map_mul, S.pushedRingHom_naturality hV'V, ha, map_mul]
  · rw [PresheafOfModules.map_smul,
      S.isDescendedSmul_descendedSmul F s hs hVW b V' hV'V a ha]
    exact (mul_smul _ _ _).symm

include hs in
/-- Acting by the unit section of `i_* 𝒪_Z` recovers the annihilated section itself. -/
lemma descendedSmul_one : S.descendedSmul F s hs (le_refl W) 1 = s := by
  refine S.descendedSmul_eq F s hs (le_refl W) 1 fun V' hV'W a ha => ?_
  have h1 : S.pushedRingHom.hom.app (op V') (a - 1) = 0 := by
    rw [map_sub, ha, map_one, map_one, sub_self]
  have h := hs V' hV'W (a - 1) h1
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

/-! ### Extending an annihilated section off the image of `Z` -/

/-- An annihilated section vanishes on every open subset disjoint from the image of `Z`, because
there the kernel ideal is the unit ideal. -/
lemma eq_zero_of_mem_sections_of_le_opensComplRange {U : Opens S.X} (t : F.val.obj (op U))
    (ht : t ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F U) {C : Opens S.X} (hCU : C ≤ U)
    (hC : C ≤ S.opensComplRange) : F.val.map (homOfLE hCU).op t = 0 := by
  have h := ht C hCU 1 (S.one_mem_kernelIdeal_of_le_opensComplRange hC)
  rwa [one_smul] at h

/-- An annihilated section over `U` extends to an annihilated section over any larger open `W`
which `U` covers up to the complement of the image of `Z`; the extension is by zero off `U`.

Applied to `W = i_! i⁻¹ U`, where `opensFunctor_opensMap_le_sup` supplies the covering
hypothesis, this says that the annihilated sections over `U` and over `i_! i⁻¹ U` agree. -/
lemma exists_mem_sections_restrict_eq {U W : Opens S.X} (hUW : U ≤ W)
    (hcover : W ≤ U ⊔ (W ⊓ S.opensComplRange)) (t : F.val.obj (op U))
    (ht : t ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F U) :
    ∃ r, r ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F W ∧
      F.val.map (homOfLE hUW).op r = t := by
  have hBW : W ⊓ S.opensComplRange ≤ W := inf_le_left
  have hBC : W ⊓ S.opensComplRange ≤ S.opensComplRange := inf_le_right
  let Wf : Bool → Opens S.X := fun c =>
    match c with
    | true => U
    | false => W ⊓ S.opensComplRange
  have hWfle : ∀ c, Wf c ≤ W := by
    rintro (_ | _)
    · exact hBW
    · exact hUW
  have hcov : W ≤ iSup Wf :=
    le_trans hcover (sup_le (le_iSup Wf true) (le_iSup Wf false))
  have hcompat : ∀ c c' : Bool,
      F.val.map (homOfLE (inf_le_left : Wf c ⊓ Wf c' ≤ Wf c)).op
          (match c with | true => t | false => 0) =
        F.val.map (homOfLE (inf_le_right : Wf c ⊓ Wf c' ≤ Wf c')).op
          (match c' with | true => t | false => 0) := by
    rintro (_ | _) (_ | _)
    · exact (map_zero _).trans (map_zero _).symm
    · exact (map_zero _).trans
        (S.eq_zero_of_mem_sections_of_le_opensComplRange F t ht inf_le_right
          (inf_le_left.trans hBC)).symm
    · exact (S.eq_zero_of_mem_sections_of_le_opensComplRange F t ht inf_le_left
        (inf_le_right.trans hBC)).trans (map_zero _).symm
    · rfl
  obtain ⟨r, hr⟩ := S.exists_gluing F Wf W hWfle hcov
    (fun c => match c with | true => t | false => 0) hcompat
  have hrU : F.val.map (homOfLE hUW).op r = t := hr true
  have hrB : F.val.map (homOfLE hBW).op r = 0 := hr false
  refine ⟨r, fun W' hW'W a ha => ?_, hrU⟩
  refine S.eq_of_locally_eq_of_mem F W' _ _ fun x hx => ?_
  rcases hcover (hW'W hx) with hxU | hxB
  · have hCW : W' ⊓ U ≤ W := inf_le_right.trans hUW
    refine ⟨W' ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
    rw [S.map_smul_map F hW'W (inf_le_left : W' ⊓ U ≤ W') hCW,
      ← map_map_of_le F.val hUW (inf_le_right : W' ⊓ U ≤ U) hCW, hrU]
    exact (ht (W' ⊓ U) inf_le_right _ (S.map_mem_kernelIdeal _ a ha)).trans (map_zero _).symm
  · have hCW : W' ⊓ (W ⊓ S.opensComplRange) ≤ W := inf_le_left.trans hW'W
    have hz : F.val.map (homOfLE hCW).op r = 0 := by
      rw [← map_map_of_le F.val hBW
        (inf_le_right : W' ⊓ (W ⊓ S.opensComplRange) ≤ W ⊓ S.opensComplRange) hCW, hrB]
      exact map_zero _
    refine ⟨W' ⊓ (W ⊓ S.opensComplRange), inf_le_left, ⟨hx, hxB⟩, ?_⟩
    rw [S.map_smul_map F hW'W (inf_le_left : W' ⊓ (W ⊓ S.opensComplRange) ≤ W') hCW]
    exact (S.smul_map_eq_zero_of_map_eq_zero F hCW _ r hz).trans (map_zero _).symm

end ClosedQuotientMorphismOfRingedSpaces

end RingedSpaceModuleAdjunction

end
