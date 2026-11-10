module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksCore.CategoryTheory.Subobject.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Essential monomorphisms and essential epimorphisms

A monomorphism `i : A ⟶ B` is *essential* when every nonzero subobject of `B` meets the image
of `i`; dually an epimorphism `f : X ⟶ Y` is *essential* when no proper subobject of `X` is
carried onto all of `Y`. The first notion is the one that makes `B` an *essential extension* of
`A`, and it is the basic ingredient in the construction of injective hulls; the second is the
ingredient in the notion of a projective cover.

Both notions are defined for an arbitrary category with the limits the definition mentions —
images for the epimorphism version, pullbacks and a zero object for the monomorphism version —
so in particular they apply in every abelian category. The sources state them for abelian
categories only.

The closure properties proved here are the categorical half of the theory: essential
monomorphisms and essential epimorphisms are closed under composition, essentiality of a
subobject is inherited by its intersections, an essential epimorphism stays essential after
dividing out the image of the kernel of another epimorphism out of the same object, and a
filtered colimit of essential extensions of a fixed object is again an essential extension.

For modules the categorical definition is elementwise: a submodule `M ⊆ N` is essential exactly
when every nonzero `x : N` has a nonzero multiple `r • x` lying in `M`.

## Main definitions

* `Module.IsEssentialEpi` — `f` is an epimorphism and the direct image of every proper subobject
  of its source is a proper subobject of its target.
* `Module.IsEssentialMono` — every nonzero subobject of the target of the monomorphism `i` has
  nonzero intersection with the image of `i`.

## Main results

* `Module.isEssentialEpi_comp`, `Module.isEssentialMono_comp` — closure under composition.
* `Module.isEssentialMono_pullback` — the intersection of an essential subobject with any
  subobject is essential in the latter.
* `Module.isEssentialMono_subtype_iff` — the elementwise criterion for submodules.
* `Module.essentialEpi_epiDesc_cokernel` — essential epimorphisms descend to the quotient by the
  image of the kernel of an epimorphism with the same source.
* `Module.isEssentialMono_colimit` — the map of a module into the filtered colimit of a
  compatible system of essential extensions is essential.

## References

* [Stacks Project, Tag 08XJ](https://stacks.math.columbia.edu/tag/08XJ)
* [Stacks Project, Tag 08XK](https://stacks.math.columbia.edu/tag/08XK)
* [Stacks Project, Tag 08XL](https://stacks.math.columbia.edu/tag/08XL)
* [Stacks Project, Tag 08XM](https://stacks.math.columbia.edu/tag/08XM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w z v u

namespace Module

/-- A morphism is an essential epimorphism if it is an epimorphism and the direct image of
every proper subobject of its source is proper. -/
@[stacks 08XJ "essential_surjection"]
abbrev IsEssentialEpi {C : Type u} [Category.{v} C] [HasImages C] {X Y : C} (f : X ⟶ Y) : Prop :=
  Epi f ∧ ∀ X' : Subobject X, X' ≠ ⊤ → (Subobject.«exists» f).obj X' ≠ ⊤

/-- A monomorphism is essential if every nonzero subobject of its codomain has nonzero
intersection with its image. -/
@[stacks 08XJ "essential_injection"]
abbrev IsEssentialMono {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [HasPullbacks 𝒜]
    {A B : 𝒜} (i : A ⟶ B) [Mono i] : Prop :=
  ∀ B' : Subobject B, B' ≠ ⊥ → B' ⊓ Subobject.mk i ≠ ⊥

section Surjections

variable {𝒜 : Type u} [Category.{v} 𝒜]

/-- The restriction of `f` to a subobject `S` of its source is an epimorphism precisely when the
direct image of `S` under `f` is the whole of the target. -/
theorem epi_arrow_comp_iff_exists_obj_eq_top [HasImages 𝒜] [HasEqualizers 𝒜] [Balanced 𝒜]
    {X Y : 𝒜} (f : X ⟶ Y) (S : Subobject X) :
    Epi (S.arrow ≫ f) ↔ (Subobject.«exists» f).obj S = ⊤ := by
  rw [Subobject.exists_eq_imageSubobject]
  refine ⟨fun _ ↦ Subobject.imageSubobject_eq_top_of_epi _, fun h ↦ ?_⟩
  have : IsIso (imageSubobject (S.arrow ≫ f)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 h
  rw [← imageSubobject_arrow_comp (S.arrow ≫ f)]
  infer_instance

/-- A morphism whose composite with an essential epimorphism is an epimorphism is itself an
epimorphism. -/
theorem epi_of_comp_isEssentialEpi [Abelian 𝒜] {X Y Z : 𝒜} (h : Z ⟶ X) (f : X ⟶ Y)
    (hf : IsEssentialEpi f) [Epi (h ≫ f)] : Epi h := by
  have hfac : factorThruImageSubobject h ≫ (imageSubobject h).arrow ≫ f = h ≫ f := by
    rw [← Category.assoc, imageSubobject_arrow_comp]
  have htop : (Subobject.«exists» f).obj (imageSubobject h) = ⊤ :=
    (epi_arrow_comp_iff_exists_obj_eq_top f _).1 (epi_of_epi_fac hfac)
  have himage : imageSubobject h = ⊤ := of_not_not fun hne ↦ hf.2 _ hne htop
  have : IsIso (imageSubobject h).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 himage
  rw [← imageSubobject_arrow_comp h]
  infer_instance

/-- The composite of two essential epimorphisms is an essential epimorphism. -/
@[stacks 08XK "essential_surjection_comp"]
theorem isEssentialEpi_comp [HasImages 𝒜] {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsEssentialEpi f) (hg : IsEssentialEpi g) : IsEssentialEpi (f ≫ g) := by
  refine ⟨epi_comp' hf.1 hg.1, ?_⟩
  intro X' hX'
  apply ne_top_of_le_ne_top (hg.2 _ (hf.2 X' hX'))
  let U : Subobject B := (Subobject.«exists» f).obj X'
  let V : Subobject C := (Subobject.«exists» g).obj U
  have hU : U.Factors (X'.arrow ≫ f) := by
    simpa [U, Subobject.exists_eq_imageSubobject] using
      Limits.imageSubobject_factors_comp_self (X'.arrow ≫ f) (𝟙 (X' : 𝒜))
  have hV : V.Factors (U.arrow ≫ g) := by
    simpa [V, Subobject.exists_eq_imageSubobject] using
      Limits.imageSubobject_factors_comp_self (U.arrow ≫ g) (𝟙 (U : 𝒜))
  exact Subobject.exists_le_of_comm (f ≫ g)
    (U.factorThru (X'.arrow ≫ f) hU ≫ V.factorThru (U.arrow ≫ g) hV)
    (by change _ ≫ V.arrow = _; simp [Subobject.factorThru_arrow, Category.assoc])

end Surjections

section Injections

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [HasPullbacks 𝒜]

/-- The composite of two essential monomorphisms is essential. -/
@[stacks 08XK "essential_extension_trans"]
theorem isEssentialMono_comp {A B C : 𝒜} (i : A ⟶ B) (j : B ⟶ C) [Mono i] [Mono j]
    (hi : IsEssentialMono i) (hj : IsEssentialMono j) : IsEssentialMono (i ≫ j) := by
  intro X hX
  let P : Subobject B := (Subobject.pullback j).obj X
  have hPX : (Subobject.map j).obj P = X ⊓ Subobject.mk j := by
    rw [inf_comm]
    change (Subobject.map j).obj P = (Subobject.inf.obj (Quotient.mk'' (MonoOver.mk j))).obj X
    exact (Subobject.inf_eq_map_pullback' (MonoOver.mk j) X).symm
  have hP : P ≠ ⊥ := fun h => hj X hX (by rw [← hPX, h, Subobject.map_bot])
  rw [show X ⊓ Subobject.mk (i ≫ j) =
      (Subobject.map j).obj (P ⊓ Subobject.mk i) by
    rw [Subobject.inf_map, hPX, Subobject.map_mk, inf_assoc,
      inf_eq_right.mpr (Subobject.mk_le_mk_of_comm i (by simp))]]
  exact fun h => hi P hP (Subobject.map_obj_injective j (h.trans (Subobject.map_bot j).symm))

/-- The intersection of an essential subobject with another subobject is essential in that
subobject. -/
@[stacks 08XK "essential_extension_intersection"]
theorem isEssentialMono_pullback {B : 𝒜} (A C : Subobject B) (hA : IsEssentialMono A.arrow) :
    IsEssentialMono ((Subobject.pullback C.arrow).obj A).arrow := by
  intro D hD
  let E : Subobject B := (Subobject.map C.arrow).obj D
  have hE : E ≠ ⊥ := fun h ↦
    hD (Subobject.map_obj_injective C.arrow (by simpa [E, Subobject.map_bot] using h))
  have hEC : E ≤ C := by
    simpa [E, Subobject.map_top] using (Subobject.map C.arrow).monotone (le_top : D ≤ ⊤)
  have hm : (Subobject.map C.arrow).obj (D ⊓ (Subobject.pullback C.arrow).obj A) =
      E ⊓ A := by
    rw [Subobject.inf_map, ← Subobject.inf_eq_map_pullback C A]
    rw [← inf_assoc, inf_eq_left.mpr hEC]
  intro h
  apply (hA E hE)
  rw [Subobject.mk_arrow, ← hm]
  simpa only [Subobject.mk_arrow, Subobject.map_bot] using
    congrArg (Subobject.map C.arrow).obj h

end Injections

private lemma subobjectModule_mk_eq_range {R : Type u} [Ring R]
    {A B : ModuleCat.{z, u} R} (f : A ⟶ B) [Mono f] :
    ModuleCat.subobjectModule B (Subobject.mk f) = LinearMap.range f.hom := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact ⟨(Subobject.underlyingIso f).hom y,
      ConcreteCategory.congr_hom (Subobject.underlyingIso_hom_comp_eq_mk f) y⟩
  · rintro x ⟨y, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv y, ?_⟩
    simp

private lemma isEssentialMono_iff_smul_mem_range {R : Type u} [Ring R]
    {A B : ModuleCat.{z, u} R} (f : A ⟶ B) [Mono f] :
    IsEssentialMono f ↔
      ∀ x : B, x ≠ 0 → ∃ r : R, r • x ∈ LinearMap.range f.hom ∧ r • x ≠ 0 := by
  rw [← subobjectModule_mk_eq_range f]
  constructor
  · intro h x hx
    let P : Submodule R B := R ∙ x
    have hP : P ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨x, Submodule.mem_span_singleton_self x, hx⟩
    have hcat := h ((ModuleCat.subobjectModule B).symm P) (by
      intro hbot
      apply hP
      have := congrArg (ModuleCat.subobjectModule B) hbot
      rw [OrderIso.apply_symm_apply] at this
      exact this.trans (ModuleCat.subobjectModule B).map_bot)
    have hmeet : P ⊓ ModuleCat.subobjectModule B (Subobject.mk f) ≠ ⊥ := by
      intro hbot
      apply hcat
      apply (ModuleCat.subobjectModule B).injective
      rw [OrderIso.map_inf, OrderIso.apply_symm_apply]
      exact hbot.trans (ModuleCat.subobjectModule B).map_bot.symm
    obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt ((bot_lt_iff_ne_bot).2 hmeet)
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_inf.mp y.2).1
    exact ⟨r, by simpa [hr] using (Submodule.mem_inf.mp y.2).2,
      by simpa [hr] using fun hzero ↦ hy (Subtype.ext hzero)⟩
  · intro h B' hB' hbot
    have hbot' := congrArg (ModuleCat.subobjectModule B) hbot
    rw [OrderIso.map_inf] at hbot'
    have hBsub : ModuleCat.subobjectModule B B' ≠ ⊥ := by
      intro hz
      apply hB'
      apply (ModuleCat.subobjectModule B).injective
      exact hz.trans (ModuleCat.subobjectModule B).map_bot.symm
    obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt ((bot_lt_iff_ne_bot).2 hBsub)
    have hx0 : x.1 ≠ 0 := fun hx0 ↦ hx (Subtype.ext hx0)
    obtain ⟨r, hrange, hr0⟩ := h x.1 hx0
    have hz : r • x.1 ∈ ModuleCat.subobjectModule B B' ⊓
        ModuleCat.subobjectModule B (Subobject.mk f) :=
      ⟨by simpa using Submodule.smul_mem _ r x.2, hrange⟩
    rw [hbot', (ModuleCat.subobjectModule B).map_bot] at hz
    exact hr0 (by simpa using hz)

/-- A submodule inclusion is essential if and only if every nonzero element of the ambient
module has a nonzero scalar multiple lying in the submodule. -/
@[stacks 08XM]
theorem isEssentialMono_subtype_iff {R : Type u} [Ring R]
    {N : ModuleCat.{v} R} (M : Submodule R N) :
    IsEssentialMono (ModuleCat.ofHom M.subtype) ↔
      ∀ x : N, x ≠ 0 → ∃ f : R, (f • x ∈ M ∧ f • x ≠ 0) := by
  simpa using isEssentialMono_iff_smul_mem_range (ModuleCat.ofHom M.subtype)

section Quotient

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : C} (f : A ⟶ B) (q : A ⟶ D) [Epi q]

private lemma epi_of_epi_comp_of_kernel_factor {X Y Z : C} (p : Y ⟶ Z) [Epi p]
    (h : X ⟶ Y) (hh : Epi (h ≫ p)) (k : kernel p ⟶ Abelian.image h)
    (hk : k ≫ Abelian.image.ι h = kernel.ι p) : Epi h := by
  apply Preadditive.epi_of_cancel_zero h
  intro T u hu
  have hker : kernel.ι p ≫ u = 0 := by
    rw [← hk, Category.assoc, (Abelian.image.ι_comp_eq_zero h u).2 hu]
    simp
  have hd : Abelian.epiDesc p u hker = 0 :=
    zero_of_epi_comp (h ≫ p) (by rwa [Category.assoc, Abelian.comp_epiDesc])
  rw [← Abelian.comp_epiDesc p u hker, hd, comp_zero]

/-- The quotient of an essential epimorphism by the image of the kernel of an epimorphism
with the same source remains an essential epimorphism. -/
@[stacks 08XK "essential_surjection_quotient"]
theorem essentialEpi_epiDesc_cokernel (hf : IsEssentialEpi f) :
    IsEssentialEpi
      (Abelian.epiDesc q (f ≫ cokernel.π (kernel.ι q ≫ f))
        (by simpa only [Category.assoc] using
          (cokernel.condition (kernel.ι q ≫ f)))) := by
  let t := kernel.ι q ≫ f
  let π := cokernel.π t
  have hzero : kernel.ι q ≫ (f ≫ π) = 0 := by
    rw [← Category.assoc]
    exact cokernel.condition t
  let g := Abelian.epiDesc q (f ≫ π) hzero
  have : Epi f := hf.1
  have hgfac : q ≫ g = f ≫ π := Abelian.comp_epiDesc q (f ≫ π) hzero
  refine ⟨epi_of_epi_fac hgfac, ?_⟩
  intro S hS hSgTop
  let S' := (Subobject.pullback q).obj S
  let h := S'.arrow ≫ f
  have hSg : Epi (S.arrow ≫ g) := (epi_arrow_comp_iff_exists_obj_eq_top g S).2 hSgTop
  have hPull : Epi (Subobject.pullbackπ q S) := by
    rw [← (Subobject.isPullback q S).isoPullback_hom_fst]
    infer_instance
  have hCompEq : h ≫ π = Subobject.pullbackπ q S ≫ S.arrow ≫ g := by
    dsimp [h]
    rw [Category.assoc, ← hgfac]
    simpa only [Category.assoc] using congrArg (fun x => x ≫ g) (Subobject.isPullback q S).w.symm
  have hh : Epi (h ≫ π) := by
    rw [hCompEq]
    infer_instance
  let k : kernel π ⟶ Abelian.image h :=
    kernel.lift (cokernel.π h) (Abelian.image.ι t) (by
      rw [Abelian.image.ι_comp_eq_zero t]
      let pb := Subobject.isPullback q S
      let kq : kernel q ⟶ S' := pb.lift 0 (kernel.ι q) (by simp)
      have hkq : kq ≫ S'.arrow = kernel.ι q := pb.lift_snd _ _ _
      change t ≫ cokernel.π h = 0
      rw [show t = kq ≫ h by simp [t, h, ← hkq, Category.assoc]]
      simp [h, Category.assoc])
  have hk : k ≫ Abelian.image.ι h = kernel.ι π := by
    dsimp [k, Abelian.image.ι, π, t]
    simp
  have hhEpi : Epi h := epi_of_epi_comp_of_kernel_factor π h hh k hk
  have hS'proper : S' ≠ ⊤ := fun htop ↦ by
    have : IsIso ((Subobject.pullback q).obj S).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 htop
    have : Epi S.arrow := epi_of_epi_fac (Subobject.isPullback q S).w
    exact hS ((Subobject.isIso_arrow_iff_eq_top S).mp (isIso_of_mono_of_epi S.arrow))
  exact (hf.2 S' hS'proper) ((epi_arrow_comp_iff_exists_obj_eq_top f S').1 hhEpi)

end Quotient

section FilteredColimit

noncomputable section

-- The abelian finite-limits instance is pinned at a high priority: the `ModuleCat`
-- countable-limits API in scope supplies a second, definitionally equal instance.
attribute [local instance 10000] CategoryTheory.Abelian.hasFiniteLimits

/-- In a compatible system of essential monomorphisms out of a fixed module, every transition
map is injective. -/
private theorem injective_map_of_isEssentialMono {R : Type u} [Ring R] {J : Type*} [Category J]
    {M : ModuleCat.{z, u} R} {E : J ⥤ ModuleCat.{z, u} R} (ι : (Functor.const J).obj M ⟶ E)
    (hι : ∀ j, ∃ h : Mono (ι.app j),
      let _ : Mono (ι.app j) := h
      IsEssentialMono (ι.app j))
    ⦃a b : J⦄ (q : a ⟶ b) : Function.Injective (E.map q) := by
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  by_contra hne
  obtain ⟨ha, hessential⟩ := hι a
  obtain ⟨r, ⟨m, hm⟩, hr0⟩ :=
    (isEssentialMono_iff_smul_mem_range (ι.app a)).mp hessential (x - y) hne
  have hzero : E.map q (r • (x - y)) = 0 := by
    rw [map_smul, map_sub, hxy, smul_zero]
  have hnat : E.map q (ι.app a m) = ι.app b m := by
    simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom (ι.naturality q) m).symm
  have hm0 : m = 0 := (ModuleCat.mono_iff_injective (ι.app b)).mp (hι b).choose (by
    rw [← hnat, hm, hzero, map_zero])
  exact hr0 (by rw [← hm, hm0, map_zero])

/-- If all transition maps of a filtered diagram of modules are injective, so is every
coprojection into its colimit. -/
private theorem injective_colimit_ι_of_injective_map {R : Type u} [Ring R] {J : Type*} [Category J]
    [IsFiltered J] {E : J ⥤ ModuleCat.{z, u} R} [HasColimit E]
    [PreservesColimit E (forget (ModuleCat.{z, u} R))]
    (hE : ∀ ⦃a b : J⦄ (q : a ⟶ b), Function.Injective (E.map q)) (a : J) :
    Function.Injective (colimit.ι E a) := by
  intro x y hxy
  obtain ⟨b, q₁, q₂, hq⟩ := Concrete.colimit_exists_of_rep_eq E x y hxy
  let e := IsFiltered.coeqHom q₁ q₂
  have hq' := congrArg (fun z ↦ E.map e z) hq
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    IsFiltered.coeq_condition q₁ q₂] at hq'
  exact hE (q₂ ≫ e) hq'

/-- For a natural transformation from a constant functor on a filtered category, the composite
of a component with the coprojection into the colimit does not depend on the index. -/
private theorem app_comp_colimit_ι_eq {C : Type*} [Category C] {J : Type*} [Category J]
    [IsFilteredOrEmpty J] {X : C} {E : J ⥤ C} [HasColimit E] (ι : (Functor.const J).obj X ⟶ E)
    (j k : J) : ι.app j ≫ colimit.ι E j = ι.app k ≫ colimit.ι E k := by
  calc
    ι.app j ≫ colimit.ι E j =
        ι.app (IsFiltered.max j k) ≫ colimit.ι E (IsFiltered.max j k) := by
      rw [← colimit.w E (IsFiltered.leftToMax j k), ← Category.assoc,
        ← ι.naturality (IsFiltered.leftToMax j k)]
      simp
    _ = ι.app k ≫ colimit.ι E k := by
      rw [← colimit.w E (IsFiltered.rightToMax j k), ← Category.assoc,
        ← ι.naturality (IsFiltered.rightToMax j k)]
      simp

/-- A compatible filtered system of essential embeddings of a module induces an essential
embedding into its colimit. -/
@[stacks 08XL]
theorem isEssentialMono_colimit {R : Type u} [Ring R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (M : ModuleCat.{max v w u, u} R)
    (E : Functor J (ModuleCat.{max v w u, u} R)) [HasColimit E]
    (ι : (Functor.const J).obj M ⟶ E)
    (hι : ∀ j, ∃ h : Mono (ι.app j),
      let _ : Mono (ι.app j) := h
      IsEssentialMono (ι.app j))
    (j : J) :
    ∃ h : Mono (ι.app j ≫ colimit.ι E j),
      let _ : Mono (ι.app j ≫ colimit.ι E j) := h
      IsEssentialMono (ι.app j ≫ colimit.ι E j) := by
  let e := (ShrinkHoms.equivalence.{max (max u v) w} J).trans <|
    Shrink.equivalence.{max (max u v) w, max (max u v) w} (ShrinkHoms.{v} J)
  let := IsFiltered.of_equivalence e
  let : PreservesColimitsOfShape J (forget AddCommGrpCat.{max (max u v) w}) :=
    preservesColimitsOfShape_of_equiv e.symm _
  let : PreservesColimit E
      (forget₂ (ModuleCat.{max v w u, u} R) AddCommGrpCat.{max (max u v) w}) := inferInstance
  let : PreservesColimit (E ⋙ forget₂ (ModuleCat.{max v w u, u} R)
      AddCommGrpCat.{max (max u v) w}) (forget AddCommGrpCat.{max (max u v) w}) := inferInstance
  let : PreservesColimit E (forget₂ (ModuleCat.{max v w u, u} R)
      AddCommGrpCat.{max (max u v) w} ⋙ forget AddCommGrpCat.{max (max u v) w}) := inferInstance
  let : PreservesColimit E (forget (ModuleCat.{max v w u, u} R)) := by
    change PreservesColimit E (forget₂ (ModuleCat.{max v w u, u} R)
      AddCommGrpCat.{max (max u v) w} ⋙ forget AddCommGrpCat.{max (max u v) w})
    infer_instance
  have hcolimit_mono :=
    injective_colimit_ι_of_injective_map (injective_map_of_isEssentialMono ι hι)
  have hmono : Mono (ι.app j ≫ colimit.ι E j) :=
    (ModuleCat.mono_iff_injective _).mpr fun _ _ h ↦
      (ModuleCat.mono_iff_injective (ι.app j)).mp (hι j).choose (hcolimit_mono j h)
  refine ⟨hmono, ?_⟩
  apply (isEssentialMono_iff_smul_mem_range _).mpr
  intro x hx
  obtain ⟨k, y, rfl⟩ := Concrete.colimit_exists_rep E x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨hk, hessential⟩ := hι k
  obtain ⟨r, ⟨m, hm⟩, hr0⟩ :=
    (isEssentialMono_iff_smul_mem_range (ι.app k)).mp hessential y hy
  refine ⟨r, ?_, fun hzero ↦ hr0 (hcolimit_mono k (by simpa using hzero))⟩
  rw [← map_smul]
  change colimit.ι E k (r • y) ∈ _
  rw [← hm]
  exact ⟨m, by simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (app_comp_colimit_ι_eq ι j k) m⟩

end

end FilteredColimit

end Module

end
