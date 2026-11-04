module

public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSections
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Extension by zero across a two-open cover, and the comparison map of Stacks 0EG2

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf and `F` a sheaf of modules. The quotients
`F / Iⁿ F` of `Stacks.Algebraization.adicQuotientSystem` vanish off the support of `I`, so
restricting a section of `F / Iⁿ F` to an open `V` containing that support loses nothing — the
section extends back by zero on the complement of the support.

That is what makes the comparison of Tag 0EG2 well defined. A section of `F` on a neighbourhood
`V` of the formal locus `U ∩ V(I)` reduces to a section of `F / Iⁿ F` on `V` only, while the
formal sections of `Stacks.Algebraization.formalSections` are sections on all of `U`; inverting
the restriction isomorphism turns the first into the second, compatibly in `n` and in `V`, and
the resulting cocone defines `Stacks.Algebraization.comparisonMap`.

## Main results

* `Stacks.Sheaf.isIso_res_of_subsingleton` — **extension by zero across a two-open cover.** If a
  sheaf of abelian groups has no nonzero sections on any open contained in `W`, and `T ≤ V ⊔ W`,
  then restriction along `V ≤ T` is an isomorphism. Injectivity is separatedness; surjectivity
  glues the given section on `V` to the zero section on `W`.
* `Stacks.SheafOfModules.subsingleton_sections_cokernel_submodule_ι` — a sheaf quotient
  `F / N` has only the zero section over an open on which `N` is everything.
* `Stacks.Algebraization.isIso_adicQuotientSystem_res_of_support_le` — restriction of
  `(adicQuotientSystem I F).obj (op n)` from `⊤` to an open containing `I.support` is an
  isomorphism.
* `Stacks.Algebraization.support_baseIdealSheaf_le` — the support of `I · 𝒪_X` lies over the
  zero locus of `I`.
* `Stacks.Algebraization.comparisonMap` — the canonical comparison from sections near the formal
  locus to formal sections, and `Stacks.Algebraization.comparisonMap_restrict`, which identifies
  it after restriction with the quotient map to `F / Iⁿ F`.

## Implementation notes

The general gluing lemma is stated for a presheaf together with a proof that it is a sheaf,
rather than for a bundled `TopCat.Sheaf`, because every consumer here arrives with
`AlgebraicGeometry.Scheme.Modules.isSheaf` in hand. The hypothesis is phrased as "every open
below `W` has subsingleton sections" rather than as the two instances actually used (`W` itself
and `V ⊓ W`), because `IsCompatible` presents the overlap in both orders (`V ⊓ W` and `W ⊓ V`)
and because the consumers prove the uniform statement anyway.

The vanishing of the quotient off the support is obtained on stalks. The stalk functor of
`AlgebraicGeometry.SheafOfModules` preserves colimits, hence epimorphisms, so the stalk of
`cokernel N.ι` is covered by the stalk of `F`, which the stalk of `N` already covers whenever
`N` is everything on a neighbourhood basis of the point; the composite is zero, so the stalk of
the quotient vanishes. Sections over an open all of whose stalks vanish are equal by
`TopCat.Presheaf.section_ext`.

`Epi` for `X.Modules` and for `SheafOfModules X.ringCatSheaf` are two separately declared
instances of one category, so the epimorphism of the cokernel projection is transported by hand;
this is the same crossing as `AlgebraicGeometry.Scheme.Modules`-vs-`SheafOfModules` elsewhere in
this subtree.

The comparison is built out of two named abbreviations, `projNearVanishing` and
`resNearVanishing`, whose types are written in the `sectionsNearVanishing`/`formalSections`
spelling rather than in the `Γ(·, ·)` spelling of `AlgebraicGeometry.Scheme.Modules.presheaf`.
That is not cosmetic: the two spellings differ by unfolding a semireducible `def`, and `rw`
builds its motive at `implicit` transparency, so without the ascription the reassociation and
cancellation steps in the cone and cocone naturality proofs fail with "did not find an
occurrence" on goals that visibly contain the pattern. For the same reason the two naturality
squares and the functoriality of restriction are proved as separate `theorem`s in term mode, and
`CategoryTheory.Category.id_comp` has to be applied by `exact` rather than by `rw`.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Sheaf

/-- **Extension by zero across a two-open cover.**

Let `G` be a sheaf of abelian groups on `X`, let `V`, `W` be opens covering `T`, and suppose `G`
has only the zero section on every open contained in `W`. Then restriction `Γ(T, G) ⟶ Γ(V, G)` is
an isomorphism: it is injective because a section vanishing on `V` vanishes on `W` as well, and
surjective because any section on `V` glues with the zero section on `W`. -/
theorem isIso_res_of_subsingleton {X : TopCat.{u}}
    {G : TopCat.Presheaf Ab.{u} X} (hG : G.IsSheaf)
    {T V W : Opens X} (hVT : V ≤ T) (hWT : W ≤ T) (hcover : T ≤ V ⊔ W)
    (hW : ∀ O : Opens X, O ≤ W → Subsingleton (ToType (G.obj (op O)))) :
    IsIso (G.map (homOfLE hVT).op) := by
  let 𝒢 : TopCat.Sheaf Ab.{u} X := ⟨G, hG⟩
  let U : Bool → Opens X := fun b => cond b V W
  have hsup : T ≤ iSup U := hcover.trans (by rw [iSup_bool_eq]; exact le_rfl)
  let iUT : ∀ b, U b ⟶ T := fun b => Bool.rec (homOfLE hWT) (homOfLE hVT) b
  have hcpt : ∀ sf : ∀ b, ToType (G.obj (op (U b))), TopCat.Presheaf.IsCompatible G U sf := by
    intro sf i j
    rcases i with _ | _ <;> rcases j with _ | _
    · rw [Subsingleton.elim (Opens.infLELeft (U false) (U false))
        (Opens.infLERight (U false) (U false))]
    · exact (hW _ inf_le_left).elim _ _
    · exact (hW _ inf_le_right).elim _ _
    · rw [Subsingleton.elim (Opens.infLELeft (U true) (U true))
        (Opens.infLERight (U true) (U true))]
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun s t hst => ?_, fun s => ?_⟩
  · refine 𝒢.eq_of_locally_eq' U T iUT hsup s t fun b => ?_
    rcases b with _ | _
    · exact (hW _ le_rfl).elim _ _
    · exact hst
  · obtain ⟨g, hg, -⟩ :=
      𝒢.existsUnique_gluing' U T iUT hsup (fun b => Bool.rec 0 s b) (hcpt _)
    exact ⟨g, hg true⟩

/-- A sheaf of abelian groups whose stalks vanish at every point of an open has only the zero
section over that open. -/
theorem subsingleton_sections_of_subsingleton_stalk {X : TopCat.{u}}
    {G : TopCat.Presheaf Ab.{u} X} (hG : G.IsSheaf) (O : Opens X)
    (h : ∀ x ∈ O, Subsingleton (ToType (TopCat.Presheaf.stalk G x))) :
    Subsingleton (ToType (G.obj (op O))) :=
  ⟨fun s t => TopCat.Presheaf.section_ext (⟨G, hG⟩ : TopCat.Sheaf Ab.{u} X) O s t
    fun x hx => (h x hx).elim _ _⟩

end Stacks.Sheaf

namespace Stacks.SheafOfModules

/-- If a submodule `N` of a sheaf of modules `F` is the whole of `F` on every affine open
contained in `O`, then the map `N_x ⟶ F_x` on stalks is surjective at every point `x` of `O`:
every germ is represented by a section on an affine open inside `O`, where it lies in `N`. -/
theorem surjective_stalk_submodule_ι {X : Scheme.{u}} {F : X.Modules} (N : F.Submodule)
    {O : X.Opens} (hN : ∀ U : X.affineOpens, U.1 ≤ O → N.toSubmodule.obj (op U.1) = ⊤)
    {x : X} (hx : x ∈ O) :
    Function.Surjective (ConcreteCategory.hom
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map N.ι)) := by
  intro t
  obtain ⟨U', hxU', s, hs⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf t
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := U' ⊓ O) (x := x) ⟨hxU', hx⟩
  have hmem : ConcreteCategory.hom
      (F.val.presheaf.map (homOfLE (hVle.trans inf_le_left)).op) s ∈
      N.toSubmodule.obj (op V) := by
    rw [hN ⟨V, hVaff⟩ (hVle.trans inf_le_right)]; trivial
  refine ⟨TopCat.Presheaf.germ N.toSheafOfModules.val.presheaf V x hxV ⟨_, hmem⟩, ?_⟩
  refine Eq.trans (show ConcreteCategory.hom
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map N.ι)
      (TopCat.Presheaf.germ N.toSheafOfModules.val.presheaf V x hxV ⟨_, hmem⟩) =
      ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map N.ι.val))
      (TopCat.Presheaf.germ N.toSheafOfModules.val.presheaf V x hxV ⟨_, hmem⟩) from rfl) ?_
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply' V x hxV
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map N.ι.val) ⟨_, hmem⟩).trans ?_
  exact (TopCat.Presheaf.germ_res_apply F.val.presheaf
    (homOfLE (hVle.trans inf_le_left)) x hxV s).trans hs

/-- The quotient `F / N` has vanishing stalk at every point of an open on which `N` is all of
`F`. The stalk functor of sheaves of modules preserves colimits, hence epimorphisms, so the
stalk of the quotient is covered by the stalk of `F`, which the stalk of `N` already covers;
the composite `N_x ⟶ F_x ⟶ (F/N)_x` is zero. -/
theorem subsingleton_stalk_cokernel_submodule_ι {X : Scheme.{u}} {F : X.Modules}
    (N : F.Submodule) {O : X.Opens}
    (hN : ∀ U : X.affineOpens, U.1 ≤ O → N.toSubmodule.obj (op U.1) = ⊤)
    {x : X} (hx : x ∈ O) :
    Subsingleton (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (cokernel (C := X.Modules) N.ι).presheaf x)) := by
  have hπ : Epi ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
      (cokernel.π (C := X.Modules) N.ι)) := by
    have h0 : Epi (C := X.Modules) (cokernel.π (C := X.Modules) N.ι) :=
      coequalizer.π_epi (C := X.Modules)
    have h1 : Epi (C := _root_.SheafOfModules.{u} X.ringCatSheaf)
        (cokernel.π (C := X.Modules) N.ι) :=
      ⟨fun {_Z} g h w => h0.left_cancellation g h w⟩
    exact Functor.map_epi _ _
  have hπsurj := (ModuleCat.epi_iff_surjective _).1 hπ
  have hιsurj := surjective_stalk_submodule_ι N hN hx
  refine subsingleton_of_forall_eq 0 fun a => ?_
  obtain ⟨a', rfl⟩ := hπsurj a
  obtain ⟨b, rfl⟩ := hιsurj a'
  have e : (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map N.ι ≫
      (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
        (cokernel.π (C := X.Modules) N.ι) = 0 :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
        (cokernel.condition (C := X.Modules) N.ι)).trans (Functor.map_zero _ _ _))
  exact (ConcreteCategory.comp_apply _ _ b).symm.trans (by rw [e]; simp; rfl)

/-- The quotient `F / N` has only the zero section over an open `O` on which `N` is all of `F`:
all its stalks on `O` vanish, so any two sections agree. -/
theorem subsingleton_sections_cokernel_submodule_ι {X : Scheme.{u}} {F : X.Modules}
    (N : F.Submodule) {O : X.Opens}
    (hN : ∀ U : X.affineOpens, U.1 ≤ O → N.toSubmodule.obj (op U.1) = ⊤) :
    Subsingleton (ToType ((cokernel (C := X.Modules) N.ι).presheaf.obj (op O))) :=
  Stacks.Sheaf.subsingleton_sections_of_subsingleton_stalk
    (cokernel (C := X.Modules) N.ι).isSheaf O
    fun _ hx => subsingleton_stalk_cokernel_submodule_ι N hN hx

end Stacks.SheafOfModules

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- On an affine open disjoint from the support of an ideal sheaf the ideal is the unit ideal:
every point of the open is outside the zero locus, so the basic opens of the ideal cover it.

This repeats a fact stated publicly elsewhere, as
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support` of
`StacksFrontier/AlgebraicGeometry/IdealPowerHomColimit/Restriction.lean` and as
`AlgebraicGeometry.ideal_eq_top_of_le_compl_support` of
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/Basic.lean`; neither is in this file's
import closure, and reaching either costs more than the ten lines below. -/
private theorem ideal_eq_top_of_affine_le_compl_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (W : X.affineOpens) (hW : W.1 ≤ I.support.compl) : I.ideal W = ⊤ := by
  have h : W.1 ≤ ⨆ f : (I.ideal W : Set ↑Γ(X, W.1)), X.basicOpen f.1 := by
    intro x hx
    have hxs : x ∉ I.support := hW hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := W) hx,
      Scheme.mem_zeroLocus_iff] at hxs
    obtain ⟨f, hf, hxf⟩ : ∃ f ∈ (I.ideal W : Set ↑Γ(X, W.1)), x ∈ X.basicOpen f := by
      simpa using hxs
    exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩
  simpa using W.2.self_le_iSup_basicOpen_iff.1 h

/-- Off the support of `I` the subsheaf `Iⁿ F` is all of `F`: on an affine open disjoint from
the support the ideal is the unit ideal, and `⊤ ^ n • ⊤ = ⊤`. -/
theorem idealPowerMultiple_obj_eq_top_of_le_compl_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) (U : X.affineOpens)
    (hU : U.1 ≤ I.support.compl) :
    (idealPowerMultiple I n F).toSubmodule.obj (op U.1) = ⊤ := by
  refine top_le_iff.1 ?_
  have h := Stacks.AlgebraicGeometry.IdealPower.le_idealPowerMultiple_obj I n F U
  rw [ideal_eq_top_of_affine_le_compl_support I U hU, Ideal.top_pow, Submodule.top_smul] at h
  exact h

/-- The quotient `F / Iⁿ F` has only the zero section over an open disjoint from the support
of `I`. -/
theorem subsingleton_adicQuotientSystem_sections_of_le_compl_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) {O : X.Opens} (hO : O ≤ I.support.compl) :
    Subsingleton (ToType (((adicQuotientSystem I F).obj (op n)).presheaf.obj (op O))) :=
  Stacks.SheafOfModules.subsingleton_sections_cokernel_submodule_ι
    (idealPowerMultiple I n F)
    fun _ hU => idealPowerMultiple_obj_eq_top_of_le_compl_support I n F _ (hU.trans hO)

/-- **The restriction isomorphism of an adic quotient.** If an open `V` of `X` contains the
support of the quasi-coherent ideal sheaf `I`, then restriction from `X` to `V` is an
isomorphism on sections of `F / Iⁿ F`.

This is the step that makes the comparison map of Stacks 0EG2 well defined: a section of
`F / Iⁿ F` defined only near the formal locus extends uniquely to the whole space, because the
quotient vanishes on the complement of the support of `I` and `X = V ∪ (X ∖ Supp I)`. -/
theorem isIso_adicQuotientSystem_res_of_support_le {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) (n : ℕ) {V : X.Opens} (hV : (I.support : Set X) ⊆ (V : Set X)) :
    IsIso (((adicQuotientSystem I F).obj (op n)).presheaf.map
      (homOfLE (le_top (a := V))).op) := by
  refine Stacks.Sheaf.isIso_res_of_subsingleton (W := I.support.compl)
    ((adicQuotientSystem I F).obj (op n)).isSheaf le_top le_top (fun x _ => ?_)
    fun O hO => subsingleton_adicQuotientSystem_sections_of_le_compl_support I F n hO
  by_cases h : x ∈ (I.support : Set X)
  · exact Or.inl (hV h)
  · exact Or.inr h

/-! ### The restriction isomorphism at the neighbourhoods of Stacks 0EG2 -/

open Stacks.Cohomology.FormalFunctions in
/-- A point of the support of the extended ideal sheaf `I · 𝒪_X` lies over the zero locus of
`I`: if some `a ∈ I` had nonzero image at `x`, then `x` would lie in the basic open of that
image, which is the preimage of `D(a)`. -/
theorem support_baseIdealSheaf_le {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) {x : X}
    (hx : x ∈ (baseIdealSheaf A I f).support) :
    I ≤ (f.base x).asIdeal := by
  intro a ha
  have hc : ((baseIdealSheaf A I f).support : Set X) =
      X.zeroLocus (U := ⊤) (baseIdeal A I f : Set Γ(X, ⊤)) :=
    Scheme.IdealSheafData.coe_support_ofIdealTop (baseIdeal A I f)
  have hz : x ∈ X.zeroLocus (U := ⊤) (baseIdeal A I f : Set Γ(X, ⊤)) := hc ▸ hx
  have h1 := (X.mem_zeroLocus_iff _ x).1 hz _ (mem_baseIdeal A I f ha)
  by_contra h
  refine h1 ?_
  have hb : f.base x ∈ (Spec (CommRingCat.of A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    rw [show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv) a from rfl,
      AlgebraicGeometry.basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen a _).2 h
  exact Scheme.preimage_basicOpen_top f ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) ▸ hb

/-- Every neighbourhood of the formal locus contains the support of `I · 𝒪_U`: the support lies
over `V(I)`, and the neighbourhoods of `Stacks.Algebraization.OpensNearVanishing` are exactly
the opens of `U` containing `U ∩ V(I)`. -/
theorem support_idealSheafNearVanishing_le (A : Type u) [CommRing A] (I a : Ideal A)
    (V : OpensNearVanishing A I a) :
    ((idealSheafNearVanishing A I a).support : Set (complementZeroLocus A a : Scheme)) ⊆
      (V.openSet : Set (complementZeroLocus A a : Scheme)) :=
  fun _ hx => V.contains_vanishing _ (support_baseIdealSheaf_le I _ hx)

/-- **The restriction isomorphism of Stacks 0EG2.** On a neighbourhood `V` of the formal locus
`U ∩ V(I)`, restriction from all of `U` to `V` is an isomorphism on sections of `F / Iⁿ F`.

This is what makes the comparison map below well defined: a section of `F` near the formal locus
reduces to a section of `F / Iⁿ F` on `V` only, and an element of
`Stacks.Algebraization.formalSections` records sections on all of `U`, so the comparison inverts
this isomorphism. -/
theorem isIso_quotientSystemNearVanishing_res (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a) (n : ℕ) :
    IsIso (((quotientSystemNearVanishing A I a F).obj (op n)).presheaf.map
      (homOfLE (le_top (a := V.openSet))).op) :=
  isIso_adicQuotientSystem_res_of_support_le (idealSheafNearVanishing A I a) F n
    (support_idealSheafNearVanishing_le A I a V)

/-! ### The comparison map of Stacks 0EG2 -/

/-- The quotient projection `F ⟶ F / Iⁿ F` onto the term of `adicQuotientSystem` at `n`. -/
def adicProj {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) (n : ℕᵒᵖ) :
    F ⟶ (adicQuotientSystem I F).obj n :=
  cokernel.π (C := X.Modules) (idealPowerMultiple I n.unop F).ι

/-- The quotient projections are compatible with the transitions of the tower: they form the
cone `Stacks.Algebraization.adicQuotientCone`. -/
theorem adicProj_comp_map {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules)
    {m n : ℕᵒᵖ} (h : m ⟶ n) :
    adicProj I F m ≫ (adicQuotientSystem I F).map h = adicProj I F n :=
  quotientMapOfLE_π (idealPowerMultiple_antitone I F (leOfHom h.unop))

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- Reduction modulo `Iⁿ` on sections over a neighbourhood `V` of the formal locus. -/
def projNearVanishing (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    (sectionsNearVanishing A I a F).obj V ⟶
      Γ((quotientSystemNearVanishing A I a F).obj n, V.openSet) :=
  (adicProj (idealSheafNearVanishing A I a) F n).app V.openSet

/-- Restriction of sections of `F / Iⁿ F` from all of `U` to a neighbourhood `V` of the formal
locus. It is an isomorphism, which is the content of
`Stacks.Algebraization.isIso_quotientSystemNearVanishing_res`. -/
def resNearVanishing (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    (formalSections A I a F).obj n ⟶
      Γ((quotientSystemNearVanishing A I a F).obj n, V.openSet) :=
  ((quotientSystemNearVanishing A I a F).obj n).presheaf.map
    (homOfLE (le_top (a := V.openSet))).op

/-- Restriction of sections of `F / Iⁿ F` from `U` to a neighbourhood `V` of the formal locus is
an isomorphism. -/
instance (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) : IsIso (resNearVanishing A I a F V n) :=
  isIso_quotientSystemNearVanishing_res A I a F V n.unop

/-- Restriction to `V` intertwines the transitions of `formalSections` with the transitions of
the quotient tower on `V`. -/
theorem formalSections_map_comp_resNearVanishing (V : OpensNearVanishing A I a)
    {m n : ℕᵒᵖ} (h : m ⟶ n) :
    (formalSections A I a F).map h ≫ resNearVanishing A I a F V n =
      resNearVanishing A I a F V m ≫
        ((quotientSystemNearVanishing A I a F).map h).app V.openSet :=
  (((quotientSystemNearVanishing A I a F).map h).mapPresheaf.naturality
    (homOfLE (le_top (a := V.openSet))).op).symm

/-- Reduction modulo `Iᵐ` followed by the transition to `Iⁿ` is reduction modulo `Iⁿ`. -/
theorem projNearVanishing_comp_map (V : OpensNearVanishing A I a) {m n : ℕᵒᵖ} (h : m ⟶ n) :
    projNearVanishing A I a F V m ≫
        ((quotientSystemNearVanishing A I a F).map h).app V.openSet =
      projNearVanishing A I a F V n :=
  congrArg (fun φ : F ⟶ (quotientSystemNearVanishing A I a F).obj n =>
      Scheme.Modules.Hom.app φ V.openSet)
    (adicProj_comp_map (idealSheafNearVanishing A I a) F h)

/-- Restriction from `U` to a smaller neighbourhood factors through the larger one. -/
theorem resNearVanishing_comp_res {V W : OpensNearVanishing A I a} (g : V ⟶ W) (n : ℕᵒᵖ) :
    resNearVanishing A I a F V n ≫
        ((quotientSystemNearVanishing A I a F).obj n).presheaf.map (homOfLE g.down).op =
      resNearVanishing A I a F W n :=
  (((quotientSystemNearVanishing A I a F).obj n).presheaf.map_comp
      (homOfLE (le_top (a := V.openSet))).op (homOfLE g.down).op).symm.trans
    (congrArg ((quotientSystemNearVanishing A I a F).obj n).presheaf.map
      (Subsingleton.elim _ _))

/-- Reduction modulo `Iⁿ` commutes with shrinking the neighbourhood. -/
theorem sectionsNearVanishing_map_comp_projNearVanishing
    {V W : OpensNearVanishing A I a} (g : V ⟶ W) (n : ℕᵒᵖ) :
    (sectionsNearVanishing A I a F).map g ≫ projNearVanishing A I a F W n =
      projNearVanishing A I a F V n ≫
        ((quotientSystemNearVanishing A I a F).obj n).presheaf.map (homOfLE g.down).op :=
  (adicProj (idealSheafNearVanishing A I a) F n).mapPresheaf.naturality (homOfLE g.down).op

/-- The cone over `formalSections` with vertex the sections of `F` on a single neighbourhood `V`
of the formal locus: reduce modulo `Iⁿ` on `V`, then extend to all of `U`. -/
def formalSectionsCone (V : OpensNearVanishing A I a) :
    Cone (formalSections A I a F) where
  pt := (sectionsNearVanishing A I a F).obj V
  π :=
  { app := fun n => projNearVanishing A I a F V n ≫ inv (resNearVanishing A I a F V n)
    naturality := fun m n h => by
      simp only [Functor.const_obj_map]
      rw [← cancel_mono (resNearVanishing A I a F V n), Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id, Category.assoc, Category.assoc,
        formalSections_map_comp_resNearVanishing,
        ← Category.assoc (inv (resNearVanishing A I a F V m)), IsIso.inv_hom_id,
        Category.id_comp, projNearVanishing_comp_map]
      exact CategoryTheory.Category.id_comp _ }

/-- The comparison at a single neighbourhood `V`: reduce the section modulo `Iⁿ` for every `n`
and extend from `V` to all of `U` by inverting the restriction isomorphism. -/
def comparisonAt (V : OpensNearVanishing A I a) :
    (sectionsNearVanishing A I a F).obj V ⟶ limit (formalSections A I a F) :=
  limit.lift _ (formalSectionsCone A I a F V)

/-- The `n`-th component of `comparisonAt` is reduction modulo `Iⁿ` on `V` followed by the inverse
of the restriction from `U` to `V`. -/
@[reassoc]
theorem comparisonAt_π (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    comparisonAt A I a F V ≫ limit.π (formalSections A I a F) n =
      projNearVanishing A I a F V n ≫ inv (resNearVanishing A I a F V n) :=
  limit.lift_π _ _

/-- The comparisons at the individual neighbourhoods form a cocone over
`sectionsNearVanishing`, with vertex the limit of `formalSections`. -/
def formalSectionsCocone : Cocone (sectionsNearVanishing A I a F) where
  pt := limit (formalSections A I a F)
  ι :=
  { app := fun V => comparisonAt A I a F V
    naturality := fun V W g => by
      simp only [Functor.const_obj_map]
      refine Eq.trans ?_ (CategoryTheory.Category.comp_id (comparisonAt A I a F V)).symm
      refine limit.hom_ext fun n => ?_
      rw [Category.assoc, comparisonAt_π, comparisonAt_π,
        ← cancel_mono (resNearVanishing A I a F W n), Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id, ← resNearVanishing_comp_res A I a F g n,
        Category.assoc, ← Category.assoc (inv (resNearVanishing A I a F V n)),
        IsIso.inv_hom_id, Category.id_comp,
        sectionsNearVanishing_map_comp_projNearVanishing] }

/-- **The canonical comparison map of Stacks 0EG2**, from the sections of `F` defined near the
formal locus `U ∩ V(I)` to the formal sections of `F` on all of `U`. -/
def comparisonMap :
    colimit (sectionsNearVanishing A I a F) ⟶ limit (formalSections A I a F) :=
  colimit.desc _ (formalSectionsCocone A I a F)

/-- The comparison map restricted along the colimit inclusion of a neighbourhood is the
comparison at that neighbourhood. -/
theorem colimit_ι_comp_comparisonMap (V : OpensNearVanishing A I a) :
    colimit.ι (sectionsNearVanishing A I a F) V ≫ comparisonMap A I a F =
      comparisonAt A I a F V :=
  colimit.ι_desc _ _

/-- **Stacks 0EG2, the canonical comparison.** After restriction back to a neighbourhood `V` of
the formal locus, the comparison map is the canonical quotient map to `F / Iⁿ F`: the inverse
restriction isomorphism built into `comparisonMap` cancels, leaving only `cokernel.π`. -/
theorem comparisonMap_restrict (V : OpensNearVanishing A I a) (n : ℕ) :
    colimit.ι (sectionsNearVanishing A I a F) V ≫ comparisonMap A I a F ≫
        limit.π (formalSections A I a F) (op n) ≫
        ((quotientSystemNearVanishing A I a F).obj (op n)).presheaf.map
          (homOfLE (show V.openSet ≤ ⊤ from le_top)).op =
      (adicProj (idealSheafNearVanishing A I a) F (op n)).app V.openSet := by
  show colimit.ι (sectionsNearVanishing A I a F) V ≫ comparisonMap A I a F ≫
      limit.π (formalSections A I a F) (op n) ≫ resNearVanishing A I a F V (op n) =
    projNearVanishing A I a F V (op n)
  rw [← Category.assoc, ← Category.assoc, colimit_ι_comp_comparisonMap, comparisonAt_π,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end Stacks.Algebraization

end
