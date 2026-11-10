module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.DualizingPullback
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClopen
public import StacksFrontier.AlgebraicGeometry.ClopenModules.Cohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PositivityZeroDim
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletionDiscreteValuation

/-!
# Contractions of curves with isolated points

Let `c : X ⟶ Y` be a morphism of proper schemes over a field `k` with `𝒪_Y = c_*𝒪_X` and
`R^1 c_*𝒪_X = 0`, where `X` and `Y` have dimension at most one. The schemes may have isolated
points, points `x` with `{x}` open and closed; these are where the dualizing sheaf vanishes.

## Main results

* `Stacks.Curves.DualizingPullback.isClopen_singleton_image`: `c` maps an isolated point `x` to an
  isolated point, with fibre `{x}`.
* `Stacks.Curves.DualizingPullback.isIso_unitToPushforwardObjUnit_morphismRestrict` and
  `Stacks.Curves.DualizingPullback.isZero_rightDerived_one_morphismRestrict`: the two hypotheses
  on `c` restrict to `c⁻¹(V) ⟶ V` for an open `V ⊆ Y`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Curves.DualizingPullback

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- The isolated points of a topological space, the points `x` with `{x}` open and closed. -/
def isolatedPoints (T : Type*) [TopologicalSpace T] : Set T :=
  {x | IsClopen ({x} : Set T)}

/-- A set of isolated points has the discrete topology. -/
private theorem discreteTopology_of_subset_isolatedPoints {s : Set T} (hs : s ⊆ isolatedPoints T) :
    DiscreteTopology s := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun x => ⟨{x.1}, (hs x.2).isOpen, ?_⟩
  ext y
  simp [Subtype.ext_iff]

/-- **The isolated points of a Noetherian space form an open and closed subset**: it is a union of
open singletons, and it is finite, being compact and discrete, hence a finite union of closed
singletons. -/
theorem isClopen_isolatedPoints [NoetherianSpace T] : IsClopen (isolatedPoints T) := by
  have heq : isolatedPoints T = ⋃ x ∈ isolatedPoints T, ({x} : Set T) := by
    simp
  have hdisc := discreteTopology_of_subset_isolatedPoints (subset_refl (isolatedPoints T))
  have hfin : (isolatedPoints T).Finite :=
    (NoetherianSpace.isCompact (isolatedPoints T)).finite
      (isDiscrete_iff_discreteTopology.mpr hdisc)
  rw [heq]
  exact ⟨hfin.isClosed_biUnion fun x hx => hx.isClosed, isOpen_biUnion fun x hx => hx.isOpen⟩

/-- A space splits into the open and closed set of its isolated points and its complement. -/
theorem exists_isolatedPoints_decomposition [NoetherianSpace T] :
    ∃ U Z : Opens T, U ⊓ Z = ⊥ ∧ U ⊔ Z = ⊤ ∧ (Z : Set T) = isolatedPoints T := by
  have h := isClopen_isolatedPoints (T := T)
  refine ⟨⟨(isolatedPoints T)ᶜ, h.isClosed.isOpen_compl⟩, ⟨isolatedPoints T, h.isOpen⟩,
    ?_, ?_, rfl⟩ <;> ext x <;> simp

/-- A point of an open set lies outside any open set disjoint from it. -/
private theorem notMem_of_inf_eq_bot {U Z : Opens T} (h : U ⊓ Z = ⊥) {x : T} (hx : x ∈ U) :
    x ∉ Z := fun hz => (h ▸ (⟨hx, hz⟩ : x ∈ U ⊓ Z) : x ∈ (⊥ : Opens T))

/-- A point outside an open set lies in any open set covering the space together with it. -/
private theorem mem_of_notMem_of_sup_eq_top {U Z : Opens T} (hcov : U ⊔ Z = ⊤) {x : T}
    (hx : x ∉ Z) : x ∈ U :=
  (hcov ▸ trivial : x ∈ U ⊔ Z).resolve_right hx

/-- The image of an open and closed subset of an open and closed set is open and closed. -/
private theorem isClopen_image_subtypeVal {U : Set T} (hU : IsClopen U) {s : Set U}
    (hs : IsClopen s) : IsClopen (Subtype.val '' s) :=
  ⟨hU.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hs.isClosed,
    hU.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hs.isOpen⟩

/-- **On the complement of the isolated points no point is isolated**, for the open and closed
complement `U` of the isolated points. -/
theorem not_isClopen_singleton_of_isolatedPoints {U Z : Opens T} (hdisj : U ⊓ Z = ⊥)
    (hcov : U ⊔ Z = ⊤) (hZ : (Z : Set T) = isolatedPoints T) (z : U) :
    ¬ IsClopen ({z} : Set U) := by
  intro hz
  have hU : IsClopen (U : Set T) := by
    refine ⟨?_, U.isOpen⟩
    have : (U : Set T) = (Z : Set T)ᶜ := by
      exact Set.ext fun x => ⟨fun hx => notMem_of_inf_eq_bot hdisj hx,
        fun hx => mem_of_notMem_of_sup_eq_top hcov hx⟩
    rw [this]
    exact Z.isOpen.isClosed_compl
  have h1 : z.1 ∈ (Z : Set T) := by
    rw [hZ]
    have e : ({z.1} : Set T) = Subtype.val '' ({z} : Set U) := by simp
    change IsClopen ({z.1} : Set T)
    rw [e]
    exact isClopen_image_subtypeVal hU hz
  exact notMem_of_inf_eq_bot hdisj z.2 h1

/-- A point that is not isolated lies in the complement `U` of the isolated points. -/
private theorem mem_of_not_isClopen_singleton {U Z : Opens T} (hcov : U ⊔ Z = ⊤)
    (hZ : (Z : Set T) = isolatedPoints T) {x : T} (hx : ¬ IsClopen ({x} : Set T)) : x ∈ U := by
  refine mem_of_notMem_of_sup_eq_top hcov fun h => hx ?_
  have h' : x ∈ (Z : Set T) := h
  rwa [hZ] at h'

end Topology

section LocalRings

variable {k : Type u} [Field k] {Z : Scheme.{u}}

/-- **On a proper curve without isolated points every closed point has a one-dimensional local
ring.** A closed point with zero-dimensional local ring is the generic point of an irreducible
component `{z}`; its complement is the union of the finitely many other components, so `{z}` is
open, and `z` is isolated. -/
theorem ringKrullDim_stalk_eq_one_of_forall_not_isClopen (f : Z ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim Z ≤ 1)
    (hiso : ∀ z : Z, ¬ IsClopen ({z} : Set Z)) (z : Z) (hz : IsClosed ({z} : Set Z)) :
    ringKrullDim (Z.presheaf.stalk z) = 1 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Z := { }
  refine Stacks.CurveProjectiveCompletion.ringKrullDim_stalk_eq_one_of_notMem_genericPoints k f
    hdim (U := genericPoints Z) le_rfl fun hg => hiso z ⟨hz, ?_⟩
  have hcomp : ({z} : Set Z) ∈ irreducibleComponents Z := by
    rwa [genericPoints, Set.mem_ofPred_eq, hz.closure_eq] at hg
  have heq : ({z} : Set Z)ᶜ = ⋃ C ∈ irreducibleComponents Z \ {({z} : Set Z)}, C := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_sdiff,
      exists_prop]
    constructor
    · intro hyz
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      exact fun h => hyz (h ▸ mem_irreducibleComponent : y ∈ ({z} : Set Z))
    · rintro ⟨C, ⟨hC, hCz⟩, hyC⟩ rfl
      exact hCz (hcomp.eq_of_subset hC.1 (Set.singleton_subset_iff.mpr hyC)).symm
  rw [← isClosed_compl_iff, heq]
  exact ((NoetherianSpace.finite_irreducibleComponents).subset Set.sdiff_subset).isClosed_biUnion
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

end LocalRings

section Restriction

variable {X Y : Scheme.{u}} (c : X ⟶ Y)

/-- If `𝒪_Y ⟶ c_*𝒪_X` is an isomorphism, then so is `c^♯ : 𝒪_Y(W) ⟶ 𝒪_X(c⁻¹ W)` for every open
`W`. -/
theorem isIso_app_of_isIso_unitToPushforwardObjUnit
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) (W : Y.Opens) :
    IsIso (c.app W) := by
  have hO' : IsIso (C := Y.Modules)
      (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) := hO
  let e := ((Scheme.Modules.toPresheaf Y).mapIso (@asIso _ _ _ _ _ hO')).app (op W)
  have hb : Function.Bijective (c.app W) := ConcreteCategory.bijective_of_isIso e.hom
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

/-- **`𝒪_Y = c_*𝒪_X` restricts to an open of the target**: for `V ⊆ Y` open,
`𝒪_V ⟶ (c ∣_ V)_*𝒪_{c⁻¹V}` is an isomorphism, its sections over `W ⊆ V` being those of
`𝒪_Y ⟶ c_*𝒪_X` over `W` up to the identification `c⁻¹(W) = (c ∣_ V)⁻¹(W)`. -/
theorem isIso_unitToPushforwardObjUnit_morphismRestrict
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) (V : Y.Opens) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (c ∣_ V).toRingCatSheafHom) := by
  refine isIso_unitToPushforwardObjUnit_of_forall_isIso_app _ fun W => ?_
  have : IsIso ((c ∣_ V).app W.unop) := by
    rw [morphismRestrict_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_app_of_isIso_unitToPushforwardObjUnit c hO (V.ι ''ᵁ W.unop)) (Functor.map_isIso _ _)
  exact Functor.map_isIso (forget₂ CommRingCat RingCat) ((c ∣_ V).app W.unop)

/-- **`R^1 c_*𝒪_X = 0` restricts to an open of the target**: for `V ⊆ Y` open,
`R^1 (c ∣_ V)_*𝒪_{c⁻¹V} = (R^1 c_*𝒪_X)|_V = 0`, by [Stacks, Tag 01E5]. -/
theorem isZero_rightDerived_one_morphismRestrict
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) (V : Y.Opens) :
    IsZero (((Scheme.Modules.pushforward (c ∣_ V)).rightDerived 1).obj
      (SheafOfModules.unit (c ⁻¹ᵁ V).toScheme.ringCatSheaf)) :=
  (Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι) hR1).of_iso
    (((Scheme.Modules.pushforward (c ∣_ V)).rightDerived 1).mapIso
        (Scheme.Modules.restrictUnitIso (c ⁻¹ᵁ V).ι).symm ≪≫
      (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso c V 1).app
        (SheafOfModules.unit X.ringCatSheaf))

omit c in
/-- On a scheme, an open `U` whose complement `V` is open is the basic open of a global section:
the section that is `1` on `U` and `0` on `V`. -/
theorem exists_basicOpen_eq_of_inf_eq_bot {U V : X.Opens} (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤) :
    ∃ e : Γ(X, ⊤), X.basicOpen e = U := by
  let hl := X.sheaf.isProductOfDisjoint U V hdisj
  let s : Γ(X, U ⊔ V) := hl.lift (CommRingCat.prodFan Γ(X, U) Γ(X, V)) ((1, 0) : Γ(X, U) × Γ(X, V))
  have hU : X.presheaf.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op s = 1 :=
    ConcreteCategory.congr_hom (hl.fac (CommRingCat.prodFan Γ(X, U) Γ(X, V)) ⟨WalkingPair.left⟩)
      ((1, 0) : Γ(X, U) × Γ(X, V))
  have hV : X.presheaf.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op s = 0 :=
    ConcreteCategory.congr_hom (hl.fac (CommRingCat.prodFan Γ(X, U) Γ(X, V)) ⟨WalkingPair.right⟩)
      ((1, 0) : Γ(X, U) × Γ(X, V))
  refine ⟨X.presheaf.map (homOfLE (le_of_eq hcov.symm) : ⊤ ⟶ U ⊔ V).op s, ?_⟩
  have h1 := Scheme.basicOpen_res X s (homOfLE le_sup_left : U ⟶ U ⊔ V).op
  have h2 := Scheme.basicOpen_res X s (homOfLE le_sup_right : V ⟶ U ⊔ V).op
  rw [hU, Scheme.basicOpen_one] at h1
  rw [hV, Scheme.basicOpen_zero] at h2
  rw [Scheme.basicOpen_res, top_inf_eq]
  calc X.basicOpen s = (U ⊔ V) ⊓ X.basicOpen s := (inf_eq_right.mpr (Scheme.basicOpen_le X s)).symm
    _ = U ⊓ X.basicOpen s ⊔ V ⊓ X.basicOpen s := inf_sup_right _ _ _
    _ = U := by rw [← h1, ← h2, sup_bot_eq]

/-- If `𝒪_Y = c_*𝒪_X`, an open of `Y` with empty preimage is empty: its ring of sections is that
of the empty preimage, which is zero. -/
private theorem eq_bot_of_preimage_eq_bot
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) {W : Y.Opens}
    (hW : c ⁻¹ᵁ W = ⊥) : W = ⊥ := by
  by_contra hne
  have : Nonempty W := by
    obtain ⟨w, hw⟩ := Opens.ne_bot_iff_nonempty W |>.mp hne
    exact ⟨⟨w, hw⟩⟩
  have : Subsingleton Γ(X, c ⁻¹ᵁ W) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hW)
  exact not_subsingleton Γ(Y, W) (ConcreteCategory.bijective_of_isIso
    (@asIso _ _ _ _ _ (isIso_app_of_isIso_unitToPushforwardObjUnit c hO W)).hom).1.subsingleton

/-- **An isolated point is mapped to an isolated point, with fibre the point itself**: if
`𝒪_Y = c_*𝒪_X`, `c` is closed and `{x}` is open and closed in `X`, then `{c x}` is open and closed
in `Y` and `c⁻¹{c x} = {x}`. The global section of `𝒪_X` that is `1` at `x` and `0` elsewhere comes
from a global section `t` of `𝒪_Y`, with `c⁻¹(D(t)) = {x}`; the open `D(t) ∖ {c x}` has empty
preimage, so its ring of sections vanishes and it is empty. -/
theorem isClopen_singleton_image_and_preimage_eq [UniversallyClosed c]
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) {x : X}
    (hx : IsClopen ({x} : Set X)) :
    IsClopen ({c x} : Set Y) ∧ c ⁻¹' {c x} = {x} := by
  let U : X.Opens := ⟨{x}, hx.isOpen⟩
  let V : X.Opens := ⟨{x}ᶜ, hx.isClosed.isOpen_compl⟩
  obtain ⟨e, he⟩ := exists_basicOpen_eq_of_inf_eq_bot (U := U) (V := V)
    (by ext y; simp [U, V]) (by ext y; simp [U, V])
  have hiso : IsIso c.appTop := isIso_app_of_isIso_unitToPushforwardObjUnit c hO ⊤
  let t : Γ(Y, ⊤) := inv c.appTop e
  have ht : c.appTop t = e := by
    change (inv c.appTop ≫ c.appTop) e = e
    rw [IsIso.inv_hom_id]
    rfl
  let T : Y.Opens := Y.basicOpen t
  have hT : (c ⁻¹ᵁ T : Set X) = {x} := by
    change ((c ⁻¹ᵁ Y.basicOpen t : X.Opens) : Set X) = {x}
    rw [Scheme.preimage_basicOpen_top, ht, he]
    rfl
  have hcl : IsClosed ({c x} : Set Y) := by
    rw [← Set.image_singleton]
    exact c.isClosedMap _ hx.isClosed
  have hxT : c x ∈ (T : Set Y) := by
    change x ∈ (c ⁻¹ᵁ T : Set X)
    rw [hT]
    rfl
  let W : Y.Opens := T ⊓ ⟨{c x}ᶜ, hcl.isOpen_compl⟩
  have hpre : c ⁻¹ᵁ W = ⊥ := by
    ext z
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hz1 : z ∈ (c ⁻¹ᵁ T : Set X) := hz.1
    rw [hT] at hz1
    exact hz.2 (by rw [Set.mem_singleton_iff.mp hz1]; rfl)
  have hW : W = ⊥ := eq_bot_of_preimage_eq_bot c hO hpre
  have hTeq : (T : Set Y) = {c x} := by
    ext z
    refine ⟨fun hz => ?_, fun hz => by rw [Set.mem_singleton_iff.mp hz]; exact hxT⟩
    by_contra hzx
    have : z ∈ (W : Set Y) := ⟨hz, hzx⟩
    rw [hW] at this
    exact this
  refine ⟨⟨hcl, ?_⟩, ?_⟩ <;> rw [← hTeq]
  exacts [T.isOpen, hT]

end Restriction

section Modules

variable {Z : Scheme.{u}}

/-- Tensor powers of isomorphic modules are isomorphic. -/
def tensorSheafNPowIsoOfIso {L M : Z.Modules} (e : L ≅ M) :
    (n : ℕ) → ((tensorSheafNPow Z.toRingedSpace L n : Z.Modules) ≅
      (tensorSheafNPow Z.toRingedSpace M n : Z.Modules))
  | 0 => Iso.refl _
  | n + 1 => tensorSheafMapIso Z.toRingedSpace (tensorSheafNPowIsoOfIso e n) e

/-- Restriction to an open commutes with tensor powers: `(ℒ^{⊗ n})|_W ≅ (ℒ|_W)^{⊗ n}`. -/
def restrictTensorSheafNPowIso (W : Z.Opens) (L : Z.Modules) (n : ℕ) :
    Scheme.Modules.restrict (tensorSheafNPow Z.toRingedSpace L n : Z.Modules) W.ι ≅
      (tensorSheafNPow W.toScheme.toRingedSpace (L.restrict W.ι) n : W.toScheme.Modules) :=
  (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫ pullbackTensorSheafNPowIso W.ι L n ≪≫
    tensorSheafNPowIsoOfIso ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app L).symm n

/-- Restricting to `W ⊆ U` is restricting to `U` and then to `W`. -/
def restrictRestrictIso {W U : Z.Opens} (h : W ≤ U) (M : Z.Modules) :
    M.restrict W.ι ≅ (M.restrict U.ι).restrict (Z.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (Z.homOfLE_ι h)).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorComp (Z.homOfLE h) U.ι).app M

/-- Finite local freeness of rank `r` on `U` passes to an open `W ⊆ U`. -/
theorem isFiniteLocallyFreeOfRank_restrict_of_le {W U : Z.Opens} (h : W ≤ U) (M : Z.Modules)
    (r : ℕ) [hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.restrict U.ι) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.restrict W.ι) r := by
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at hM ⊢
  exact (hM.restrict (Z.homOfLE h)).of_iso (restrictRestrictIso h M).symm

end Modules

section Dualizing

open Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **`H^1` of a tensor power of the dualizing sheaf vanishes on an open and closed piece if it
vanishes on `X`**, as `ω_U^{⊗ n} ≅ (ω_X^{⊗ n})|_U`. -/
theorem isZero_cohomologyOverField_tensorSheafNPow_dualizing_restrict
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) {U V : X.Opens} (hdisj : U ⊓ V = ⊥)
    (hcov : U ⊔ V = ⊤) {f' : U.toScheme ⟶ Spec (.of k)} [IsProper f'] (hf' : U.ι ≫ f = f')
    (n i : ℕ)
    (h : IsZero (cohomologyOverField k f
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField f) n) i)) :
    IsZero (cohomologyOverField k f'
      (tensorSheafNPow U.toScheme.toRingedSpace (dualizingSheafOverField f') n) i) :=
  (isZero_cohomologyOverField_restrict_of_isZero f hdisj hcov hf' _ i h).of_iso
    (cohomologyOverFieldIso k f' (tensorSheafNPowIsoOfIso
      (dualizingSheafOverFieldClopenIso f hdim hdisj hcov hf') n ≪≫
      (restrictTensorSheafNPowIso U _ n).symm) i)

/-- **Generating sections of a tensor power of the dualizing sheaf restrict to an open and closed
piece**, as `ω_U^{⊗ n} ≅ (ω_X^{⊗ n})|_U`. -/
def generatingSectionsTensorSheafNPowDualizingRestrict
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) {U V : X.Opens} (hdisj : U ⊓ V = ⊥)
    (hcov : U ⊔ V = ⊤) {f' : U.toScheme ⟶ Spec (.of k)} [IsProper f'] (hf' : U.ι ≫ f = f')
    (n : ℕ) (σ : SheafOfModules.GeneratingSections
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField f) n : X.Modules)) :
    SheafOfModules.GeneratingSections
      (tensorSheafNPow U.toScheme.toRingedSpace (dualizingSheafOverField f') n :
        U.toScheme.Modules) :=
  let e : Scheme.Modules.restrict
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField f) n : X.Modules) U.ι ≅
      (tensorSheafNPow U.toScheme.toRingedSpace (dualizingSheafOverField f') n :
        U.toScheme.Modules) :=
    restrictTensorSheafNPowIso U _ n ≪≫ (tensorSheafNPowIsoOfIso
      (dualizingSheafOverFieldClopenIso f hdim hdisj hcov hf') n).symm
  SheafOfModules.GeneratingSections.equivOfIso e (Scheme.Modules.generatingSectionsRestrict σ U)

/-- **The dualizing sheaf of an open and closed piece contained in `U` is finite locally free of
rank one when that of `U` is.** -/
theorem isFiniteLocallyFreeOfRank_dualizingSheafOverField_of_le
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) {U V W W' : X.Opens} (hdisj : U ⊓ V = ⊥)
    (hcov : U ⊔ V = ⊤) (hdisj' : W ⊓ W' = ⊥) (hcov' : W ⊔ W' = ⊤) (hWU : W ≤ U)
    {fU : U.toScheme ⟶ Spec (.of k)} [IsProper fU] (hfU : U.ι ≫ f = fU)
    {fW : W.toScheme ⟶ Spec (.of k)} [IsProper fW] (hfW : W.ι ≫ f = fW)
    [hU : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField fU) 1] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField fW) 1 := by
  have h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((dualizingSheafOverField f).restrict U.ι) 1 := by
    rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at hU ⊢
    exact hU.of_iso (dualizingSheafOverFieldClopenIso f hdim hdisj hcov hfU)
  have h2 := isFiniteLocallyFreeOfRank_restrict_of_le hWU (dualizingSheafOverField f) 1
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at h2 ⊢
  exact h2.of_iso (dualizingSheafOverFieldClopenIso f hdim hdisj' hcov' hfW).symm

end Dualizing

section Euler

open Stacks.Duality Stacks.AlgebraicGeometry.CurveEulerBridge

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsProper f]

/-- **`H^1(Z, ω_Z^{⊗ (n+1)}) ≠ 0` when `χ(𝒪_Z) > 0`**, for an invertible dualizing sheaf on a
proper scheme of dimension at most one: `χ(ω^{⊗ (n+1)}) = (n+1)(χ(ω) - χ(𝒪)) + χ(𝒪)
= -(2n+1) χ(𝒪) < 0`, as `χ(ω) = -χ(𝒪)`, whereas `χ = h^0 ≥ 0` if `H^1` vanished. -/
theorem not_isZero_cohomologyOverField_one_tensorSheafNPow_dualizingSheafOverField
    (hdim : topologicalKrullDim Z ≤ 1)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField f) 1]
    (hχ : 0 < @eulerCharacteristic k _ Z f _ _ (isCoherent_unit k f)) (n : ℕ) :
    ¬ IsZero (cohomologyOverField k f
      (tensorSheafNPow Z.toRingedSpace (dualizingSheafOverField f) (n + 1)) 1) := by
  intro hH1
  have hχω := eulerCharacteristic_dualizingSheafOverField k f hdim
  have hM := eulerCharacteristic_tensorSheafNPow k f hdim (dualizingSheafOverField f) (n + 1)
  let M : Z.Modules := tensorSheafNPow Z.toRingedSpace (dualizingSheafOverField f) (n + 1)
  have h2M := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f M
    (isZero_cohomologyOverField_two_le k f hdim M)
  have hM1 : Module.finrank k (cohomologyOverField k f M 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero hH1
    Module.finrank_zero_of_subsingleton
  unfold eulerCharacteristic at hM hχω hχ
  have h0 : (0 : ℤ) ≤ Module.finrank k (cohomologyOverField k f M 0) := Nat.cast_nonneg _
  rw [hM1, Nat.cast_zero, sub_zero] at h2M
  have key : (Module.finrank k (cohomologyOverField k f M 0) : ℤ) = _ := h2M.symm.trans hM
  rw [hχω] at key
  push_cast at key
  nlinarith

end Euler

section Pieces

open Stacks.Duality Stacks.AlgebraicGeometry.CurveEulerBridge

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (c : X ⟶ Y) (g : Y ⟶ Spec (.of k))

omit [Field k] in
/-- The preimages of two complementary opens are complementary. -/
theorem preimage_inf_eq_bot_and_sup_eq_top {W W' : Y.Opens} (hdisj : W ⊓ W' = ⊥)
    (hcov : W ⊔ W' = ⊤) : c ⁻¹ᵁ W ⊓ c ⁻¹ᵁ W' = ⊥ ∧ c ⁻¹ᵁ W ⊔ c ⁻¹ᵁ W' = ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [← Scheme.Hom.preimage_inf, hdisj]
    rfl
  · rw [← Scheme.Hom.preimage_sup, hcov]
    rfl

omit [Field k] in
/-- An open contained in the isolated points has the discrete topology, so dimension at most
zero. -/
theorem topologicalKrullDim_le_zero_of_subset_isolatedPoints {W : Y.Opens}
    (hW : (W : Set Y) ⊆ isolatedPoints Y) :
    topologicalKrullDim W.toScheme ≤ (0 : WithBot ℕ∞) := by
  have : DiscreteTopology W := discreteTopology_of_subset_isolatedPoints hW
  exact topologicalKrullDim_zero_of_discreteTopology W

/-- `c ∣_ W` composed with `W ⟶ Y ⟶ Spec k` is `c⁻¹(W) ⟶ X ⟶ Spec k`. -/
theorem morphismRestrict_comp_ι_comp (W : Y.Opens) :
    (c⁻¹ᵁ W).ι ≫ (c ≫ g) = (c ∣_ W) ≫ (W.ι ≫ g) := by
  rw [← Category.assoc, ← Category.assoc, morphismRestrict_ι]

/-- **No piece of positive dimension is contracted to isolated points**, given `m ≥ 1` with
`H^1(X, ω_X^{⊗ m}) = 0`: if `W ⊆ Y` is open and closed and consists of isolated points, and the
dualizing sheaf of `c⁻¹(W)` is invertible, then `W` is empty. For `W` nonempty, Leray for
`c⁻¹(W) ⟶ W` gives `χ(𝒪_{c⁻¹W}) = χ(𝒪_W) > 0`, which forces `H^1(c⁻¹W, ω^{⊗ m}) ≠ 0`
(`not_isZero_cohomologyOverField_one_tensorSheafNPow_dualizingSheafOverField`), while that group is
a direct summand of `H^1(X, ω_X^{⊗ m}) = 0`. -/
theorem eq_bot_of_subset_isolatedPoints [IsProper (c ≫ g)] [IsProper g]
    (hdimX : topologicalKrullDim X ≤ 1)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    {W W' : Y.Opens} (hdisj : W ⊓ W' = ⊥) (hcov : W ⊔ W' = ⊤)
    (hW : (W : Set Y) ⊆ isolatedPoints Y)
    [IsProper ((c ∣_ W) ≫ (W.ι ≫ g))]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualizingSheafOverField ((c ∣_ W) ≫ (W.ι ≫ g))) 1]
    (n : ℕ)
    (hH1 : IsZero (cohomologyOverField k (c ≫ g)
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1)) 1)) :
    W = ⊥ := by
  by_contra hne
  have : IsProper c := IsProper.of_comp c g
  have : IsClosedImmersion W.ι := isClosedImmersion_ι_of_inf_eq_bot hdisj hcov
  have : IsProper (W.ι ≫ g) := inferInstance
  have : CompactSpace W.toScheme := QuasiCompact.compactSpace_of_compactSpace (W.ι ≫ g)
  have : Nonempty W.toScheme := by
    obtain ⟨w, hw⟩ := (Opens.ne_bot_iff_nonempty W).mp hne
    exact ⟨⟨w, hw⟩⟩
  obtain ⟨hdisjX, hcovX⟩ := preimage_inf_eq_bot_and_sup_eq_top c hdisj hcov
  have hdimC : topologicalKrullDim (c ⁻¹ᵁ W).toScheme ≤ 1 :=
    (Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le).trans hdimX
  have hO' := isIso_unitToPushforwardObjUnit_morphismRestrict c hO W
  have hR1' := isZero_rightDerived_one_morphismRestrict c hR1 W
  have hRO := isZero_rightDerived_unit (c ∣_ W) (W.ι ≫ g) hdimC hR1'
  have θO := (nonempty_derivedPushforward_iso_of_isZero (c ∣_ W)
    (SheafOfModules.unit (c ⁻¹ᵁ W).toScheme.ringCatSheaf)
    (SheafOfModules.unit W.toScheme.ringCatSheaf)
    hRO (@asIso _ _ _ _ _ hO').symm).some
  have χO := @eulerCharacteristic_eq_of_derivedPushforwardIso k _ _ _ (c ∣_ W) (W.ι ≫ g) _ _ _
    (isCoherent_unit k ((c ∣_ W) ≫ (W.ι ≫ g))) _ (isCoherent_unit k (W.ι ≫ g)) θO
  have hpos := eulerCharacteristic_unit_pos_of_topologicalKrullDim_le_zero k (W.ι ≫ g)
    (topologicalKrullDim_le_zero_of_subset_isolatedPoints hW) (isCoherent_unit k (W.ι ≫ g))
  rw [← χO] at hpos
  exact not_isZero_cohomologyOverField_one_tensorSheafNPow_dualizingSheafOverField
    ((c ∣_ W) ≫ (W.ι ≫ g)) hdimC hpos n
    (isZero_cohomologyOverField_tensorSheafNPow_dualizing_restrict (c ≫ g) hdimX hdisjX hcovX
      (morphismRestrict_comp_ι_comp c g W) (n + 1) 1 hH1)

omit [Field k] in
/-- A point isolated in an open and closed subset is isolated in the whole space. -/
theorem isClopen_singleton_of_isClopen_singleton_subtype {U : Set X} (hU : IsClopen U) {z : U}
    (hz : IsClopen ({z} : Set U)) : IsClopen ({z.1} : Set X) := by
  have h : ({z.1} : Set X) = Subtype.val '' ({z} : Set U) := by simp
  rw [h]
  exact isClopen_image_subtypeVal hU hz

omit [Field k] in
/-- `(c^*ℳ)|_{c⁻¹V} ≅ (c ∣_ V)^*(ℳ|_V)`. -/
def restrictPullbackIso (V : Y.Opens) (M : Y.Modules) :
    ((Scheme.Modules.pullback c).obj M).restrict (c ⁻¹ᵁ V).ι ≅
      (Scheme.Modules.pullback (c ∣_ V)).obj (M.restrict V.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (c ⁻¹ᵁ V).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (c ⁻¹ᵁ V).ι c).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι c V).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (c ∣_ V) V.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (c ∣_ V)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm

/-- **A point over an isolated point is isolated**, given `m ≥ 1` with `H^1(X, ω_X^{⊗ m}) = 0` and
an invertible dualizing sheaf away from the isolated points of `X`: otherwise the fibre over the
isolated point `c x` lies in the non-isolated part, and is excluded by
`eq_bot_of_subset_isolatedPoints`. -/
private theorem isClopen_singleton_of_isClopen_singleton_image [IsProper (c ≫ g)] [IsProper g]
    (hdimX : topologicalKrullDim X ≤ 1)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    {UX ZX : X.Opens} (hdisjX : UX ⊓ ZX = ⊥) (hcovX : UX ⊔ ZX = ⊤)
    (hZX : (ZX : Set X) = isolatedPoints X)
    [IsProper (UX.ι ≫ c ≫ g)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualizingSheafOverField (UX.ι ≫ c ≫ g)) 1]
    (n : ℕ)
    (hH1 : IsZero (cohomologyOverField k (c ≫ g)
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1)) 1))
    {x : X} (hx : IsClopen ({c x} : Set Y)) : IsClopen ({x} : Set X) := by
  have : IsProper c := IsProper.of_comp c g
  by_contra hnx
  let P : Y.Opens := ⟨{c x}, hx.isOpen⟩
  let P' : Y.Opens := ⟨{c x}ᶜ, hx.isClosed.isOpen_compl⟩
  have hdisjP : P ⊓ P' = ⊥ := by ext; simp [P, P']
  have hcovP : P ⊔ P' = ⊤ := by ext; simp [P, P']
  obtain ⟨hdisjW, hcovW⟩ := preimage_inf_eq_bot_and_sup_eq_top c hdisjP hcovP
  have hWU : c ⁻¹ᵁ P ≤ UX := by
    intro w hw
    refine mem_of_not_isClopen_singleton hcovX hZX fun hw' => hnx ?_
    obtain ⟨-, hpre⟩ := isClopen_singleton_image_and_preimage_eq c hO hw'
    have : x ∈ c ⁻¹' {c w} := (show c w = c x from hw).symm
    rw [hpre, Set.mem_singleton_iff] at this
    rwa [this]
  have : IsClosedImmersion (c ⁻¹ᵁ P).ι := isClosedImmersion_ι_of_inf_eq_bot hdisjW hcovW
  have : IsProper ((c ∣_ P) ≫ (P.ι ≫ g)) := by
    rw [← morphismRestrict_comp_ι_comp]
    infer_instance
  have := isFiniteLocallyFreeOfRank_dualizingSheafOverField_of_le (c ≫ g) hdimX hdisjX hcovX
    hdisjW hcovW hWU rfl (morphismRestrict_comp_ι_comp c g P)
  have hP := eq_bot_of_subset_isolatedPoints c g hdimX hO hR1 hdisjP hcovP
    (fun z hz => by rwa [Set.mem_singleton_iff.mp hz]) n hH1
  have : c x ∈ (P : Set Y) := rfl
  rw [hP] at this
  exact this

omit [Field k] in
/-- If `𝒪_Y = c_*𝒪_X` and `c` is closed, the preimage of the non-isolated part of `Y` lies in the
non-isolated part of `X`, as `c` maps isolated points to isolated points. -/
private theorem preimage_le_of_isolatedPoints [UniversallyClosed c]
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    {UX ZX : X.Opens} (hcovX : UX ⊔ ZX = ⊤) (hZX : (ZX : Set X) = isolatedPoints X)
    {VY ZY : Y.Opens} (hdisjY : VY ⊓ ZY = ⊥) (hZY : (ZY : Set Y) = isolatedPoints Y) :
    c ⁻¹ᵁ VY ≤ UX := by
  intro x hx
  refine mem_of_not_isClopen_singleton hcovX hZX fun hxc => ?_
  obtain ⟨hcx, -⟩ := isClopen_singleton_image_and_preimage_eq c hO hxc
  have h1 : c x ∈ (ZY : Set Y) := by rwa [hZY]
  exact notMem_of_inf_eq_bot hdisjY hx h1

omit [Field k] in
/-- Two modules vanishing on the open and closed `V` are isomorphic once their restrictions to the
complement `U` are, both being pushed forward from `U`. -/
private def isoOfRestrictIsoOfIsZero {U V : X.Opens} (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤)
    {M N : X.Modules} (hM : IsZero (M.restrict V.ι)) (hN : IsZero (N.restrict V.ι))
    (e : M.restrict U.ι ≅ N.restrict U.ι) : M ≅ N :=
  haveI := Scheme.Modules.isIso_restrictAdjunction_unit_app_of_isZero hdisj hcov _ hM
  haveI := Scheme.Modules.isIso_restrictAdjunction_unit_app_of_isZero hdisj hcov _ hN
  asIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) ≪≫
    (Scheme.Modules.pushforward U.ι).mapIso e ≪≫
    (asIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app N)).symm

/-- The dualizing sheaf of a proper curve restricts to zero on an open and closed piece of
dimension at most zero. -/
private theorem isZero_restrict_dualizingSheafOverField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) {U V : X.Opens}
    (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤) [IsProper (U.ι ≫ f)]
    (hU : topologicalKrullDim U.toScheme ≤ (0 : WithBot ℕ∞)) :
    IsZero ((dualizingSheafOverField f).restrict U.ι) :=
  (isZero_dualizingSheafOverField_of_topologicalKrullDim_le_zero (U.ι ≫ f) hU).of_iso
    (dualizingSheafOverFieldClopenIso f hdim hdisj hcov rfl).symm

/-- **[Stacks, Tag 0E7P] in the presence of isolated points**, for `X` and `Y` whose dualizing
sheaves are finite locally free of rank one away from the isolated points. Let `X = U_X ⊔ Z_X`
and `Y = V_Y ⊔ Z_Y` with `Z_X`, `Z_Y` the sets of isolated points. Then:

1. `c⁻¹(Z_Y) ⊆ Z_X`: a fibre over an isolated point with a non-isolated point lies in `U_X`
   (`isClopen_singleton_image_and_preimage_eq`), and is then excluded by
   `eq_bot_of_subset_isolatedPoints`;
2. `c⁻¹(V_Y) ⊆ U_X`, as `c` maps isolated points to isolated points;
3. `c ∣_ V_Y : c⁻¹(V_Y) ⟶ V_Y` satisfies the hypotheses of
   `nonempty_pullback_iso_of_isFiniteLocallyFreeOfRank`, all of which restrict to open and
   closed pieces, so `(c ∣_ V_Y)^*ω_{V_Y} ≅ ω_{c⁻¹V_Y}`;
4. the dualizing sheaves of the zero-dimensional pieces `c⁻¹(Z_Y)` and `Z_Y` vanish, so both
   `c^*ω_Y` and `ω_X` are pushed forward from `c⁻¹(V_Y)`, where they agree by 3. -/
theorem nonempty_pullback_iso_of_isolatedPoints [IsProper (c ≫ g)] [IsProper g] [IsReduced X]
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    {UX ZX : X.Opens} (hdisjX : UX ⊓ ZX = ⊥) (hcovX : UX ⊔ ZX = ⊤)
    (hZX : (ZX : Set X) = isolatedPoints X)
    {VY ZY : Y.Opens} (hdisjY : VY ⊓ ZY = ⊥) (hcovY : VY ⊔ ZY = ⊤)
    (hZY : (ZY : Set Y) = isolatedPoints Y)
    [IsProper (UX.ι ≫ c ≫ g)] [IsProper (VY.ι ≫ g)]
    [hωU : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualizingSheafOverField (UX.ι ≫ c ≫ g)) 1]
    [hωV : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualizingSheafOverField (VY.ι ≫ g)) 1]
    (n : ℕ)
    (hH1 : IsZero (cohomologyOverField k (c ≫ g)
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1)) 1))
    (σ : SheafOfModules.GeneratingSections
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1) : X.Modules)) :
    Nonempty ((Scheme.Modules.pullback c).obj (dualizingSheafOverField g) ≅
      dualizingSheafOverField (c ≫ g)) := by
  have : IsProper c := IsProper.of_comp c g
  have hdisjY' : ZY ⊓ VY = ⊥ := by rw [inf_comm, hdisjY]
  have hcovY' : ZY ⊔ VY = ⊤ := by rw [sup_comm, hcovY]
  obtain ⟨hdisjX', hcovX'⟩ := preimage_inf_eq_bot_and_sup_eq_top c hdisjY hcovY
  obtain ⟨hdisjX'', hcovX''⟩ := preimage_inf_eq_bot_and_sup_eq_top c hdisjY' hcovY'
  -- 1. the fibres over isolated points consist of isolated points
  --    (`isClopen_singleton_of_isClopen_singleton_image`, used in step 4)
  -- 2. the preimage of the non-isolated part lies in the non-isolated part
  have hVU := preimage_le_of_isolatedPoints c hO hcovX hZX hdisjY hZY
  -- 3. the restricted contraction
  have : IsClosedImmersion (c ⁻¹ᵁ VY).ι := isClosedImmersion_ι_of_inf_eq_bot hdisjX' hcovX'
  have : IsClosedImmersion (c ⁻¹ᵁ ZY).ι := isClosedImmersion_ι_of_inf_eq_bot hdisjX'' hcovX''
  have : IsClosedImmersion ZY.ι := isClosedImmersion_ι_of_inf_eq_bot hdisjY' hcovY'
  have hf' := morphismRestrict_comp_ι_comp c g VY
  have : IsProper ((c ∣_ VY) ≫ (VY.ι ≫ g)) := by rw [← hf']; infer_instance
  have := isFiniteLocallyFreeOfRank_dualizingSheafOverField_of_le (c ≫ g) hdimX hdisjX hcovX
    hdisjX' hcovX' hVU rfl hf'
  obtain ⟨e⟩ := nonempty_pullback_iso_of_isFiniteLocallyFreeOfRank (c ∣_ VY) (VY.ι ≫ g)
    (Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le.trans hdimX)
    (Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le.trans hdimY)
    (isIso_unitToPushforwardObjUnit_morphismRestrict c hO VY)
    (isZero_rightDerived_one_morphismRestrict c hR1 VY) n
    (isZero_cohomologyOverField_tensorSheafNPow_dualizing_restrict (c ≫ g) hdimX hdisjX' hcovX'
      hf' (n + 1) 1 hH1)
    (generatingSectionsTensorSheafNPowDualizingRestrict (c ≫ g) hdimX hdisjX' hcovX' hf'
      (n + 1) σ)
  -- 4. vanishing on the isolated parts
  have hZXdim : topologicalKrullDim (c ⁻¹ᵁ ZY).toScheme ≤ (0 : WithBot ℕ∞) :=
    topologicalKrullDim_le_zero_of_subset_isolatedPoints fun x hx =>
      isClopen_singleton_of_isClopen_singleton_image c g hdimX hO hR1 hdisjX hcovX hZX n hH1
        (by have hx : c x ∈ (ZY : Set Y) := hx; rwa [hZY] at hx)
  have hZYdim : topologicalKrullDim ZY.toScheme ≤ (0 : WithBot ℕ∞) :=
    topologicalKrullDim_le_zero_of_subset_isolatedPoints (by rw [hZY])
  have hωZY := isZero_restrict_dualizingSheafOverField g hdimY hdisjY' hcovY' hZYdim
  have hωZX := isZero_restrict_dualizingSheafOverField (c ≫ g) hdimX hdisjX'' hcovX'' hZXdim
  have hpZ : IsZero (((Scheme.Modules.pullback c).obj (dualizingSheafOverField g)).restrict
      (c ⁻¹ᵁ ZY).ι) :=
    (Functor.map_isZero (Scheme.Modules.pullback (c ∣_ ZY)) hωZY).of_iso
      (restrictPullbackIso c ZY _)
  -- 5. assembly
  exact ⟨isoOfRestrictIsoOfIsZero hdisjX' hcovX' hpZ hωZX (restrictPullbackIso c VY _ ≪≫
    (Scheme.Modules.pullback (c ∣_ VY)).mapIso
      (dualizingSheafOverFieldClopenIso g hdimY hdisjY hcovY rfl).symm ≪≫ e ≪≫
    dualizingSheafOverFieldClopenIso (c ≫ g) hdimX hdisjX' hcovX' hf')⟩

end Pieces

end Stacks.Curves.DualizingPullback
