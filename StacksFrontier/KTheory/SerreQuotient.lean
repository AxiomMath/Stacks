module

public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Exact.Basic

/-!
# K-groups of a Serre quotient

Let `C` be an abelian category, `P` a Serre subcategory of `C` and `L : C ⥤ D` the quotient
functor to `D = C/P`, i.e. a localization of `C` at the morphisms whose kernel and cokernel lie
in `P`. The exact functors `P ⥤ C` and `C ⥤ D` induce an exact sequence
`K₀(P) → K₀(C) → K₀(D) → 0`, and the kernel of `K₀(P) → K₀(C)` consists of the elements
`[H⁰(M, φ, ψ)] - [H¹(M, φ, ψ)]`, where `φ, ψ` are endomorphisms of an object `M` of `C` with
`φ ∘ ψ = 0 = ψ ∘ φ` whose homology objects `H⁰ = Ker(φ)/Im(ψ)` and `H¹ = Ker(ψ)/Im(φ)` lie in
`P`.

## Main definitions

* `KZero.map F`: the homomorphism `K₀(𝒜) → K₀(ℬ)`, `[A] ↦ [F(A)]`, induced by an exact functor
  `F : 𝒜 ⥤ ℬ`.

## Main results

* `KZero.surjective_map_localization`, `KZero.exact_map_ι_map_localization`: the sequence
  `K₀(P) → K₀(C) → K₀(D) → 0` is exact.
* `KZero.map_ι_eq_zero_iff`: the description of the kernel of `K₀(P) → K₀(C)`.
* `KZero.mk_homology_eq_mk_homology`: `[H⁰(M, φ, ψ)] = [H¹(M, φ, ψ)]` in `K₀(C)`.

## Implementation notes

The quotient `C/P` is any category `D` with a functor `L : C ⥤ D` which is a localization at
`P.isoModSerre`; `D` is taken abelian and `L` additive and exact. Exactness of `L` is automatic
(Stacks, Tag 02MS) but is assumed so that `KZero.map L` can be formed.

Exactness at `K₀(C)` is proved through the universal property of `K₀(D)` rather than by comparing
formal sums: the class modulo the image of `K₀(P)` of a preimage under `L` is well defined,
because objects which become isomorphic in `D` are connected by a roof `M ← M' → M''` whose legs
have kernel and cokernel in `P`, and it is additive on short exact sequences of `D`, because
these lift to short exact sequences of `C` up to a cokernel lying in `P`. This is the argument of
the source, with the bijection between the terms of two formal sums replaced by the resulting
homomorphism `K₀(D) → K₀(C)/K₀(P)`.

For part (2), the source's complex `M⁺ ⇄ M⁻` is assembled inductively: two-periodic complexes
`M ⇄ N` with homology in `P`, with `M` and `N` biproducts of lists of objects, have pairs
`(∑[objects of M] - ∑[objects of N], [H⁰] - [H¹])` forming a subgroup of
`ℤ[Ob C] × K₀(P)`. This subgroup contains `([X], [X])` for `X` in `P` (the complex `X ⇄ 0`) and
`(r, 0)` for each short exact sequence relation `r` (the exact complex `X₂ ⇄ X₁ ⊞ X₃`). An element
of `K₀(P)` dying in `K₀(C)` thus comes from a complex whose two lists agree up to permutation, so
that `M ≅ N`, which is the source's bijection `τ`.

The two homology objects are homologies of short complexes: `H⁰(M, φ, ψ)` is the homology of
`M --ψ--> M --φ--> M` and `H¹(M, φ, ψ)` that of `M --φ--> M --ψ--> M`. The condition that the
complex becomes exact in `D` is stated in its equivalent form that both lie in `P`.

## References

* [Stacks, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

namespace KZero

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- A split short exact sequence gives the additivity relation in `K₀(𝒜)`. -/
theorem mk_of_splitting {S : ShortComplex 𝒜} (s : S.Splitting) :
    mk 𝒜 S.X₂ = mk 𝒜 S.X₁ + mk 𝒜 S.X₃ :=
  mk_of_shortExact S s.shortExact

/-- For a short complex `S : X₁ → X₂ → X₃`, `[H(S)] + [X₁] = [ker f] + [ker g]` in `K₀(𝒜)`. -/
theorem mk_homology_add_mk_X₁ (S : ShortComplex 𝒜) :
    mk 𝒜 S.homology + mk 𝒜 S.X₁ = mk 𝒜 (kernel S.f) + mk 𝒜 (kernel S.g) := by
  have e₁ : cokernel S.toCycles ≅ S.homology :=
    (cokernelIsCokernel _).coconePointUniqueUpToIso S.homologyIsCokernel
  have e₂ : kernel S.toCycles ≅ kernel S.f :=
    (kernelCompMono S.toCycles S.iCycles).symm ≪≫ kernelIsoOfEq S.toCycles_i
  have e₃ : S.cycles ≅ kernel S.g :=
    S.cyclesIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  rw [← mk_eq_of_iso e₁, ← mk_eq_of_iso e₂, ← mk_eq_of_iso e₃, mk_eq_kernel_add_image S.toCycles,
    mk_eq_image_add_cokernel S.toCycles]
  abel

/-- A homomorphism into `K₀(𝒜)` whose range contains every class `[X]` is surjective. -/
theorem surjective_of_mk_mem_range {G : Type*} [AddCommGroup G] (φ : G →+ KZero 𝒜)
    (h : ∀ X : 𝒜, mk 𝒜 X ∈ φ.range) : Function.Surjective φ := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (kZeroRelations 𝒜) x
  suffices QuotientAddGroup.mk' (kZeroRelations 𝒜) y ∈ φ.range from this
  induction y using FreeAbelianGroup.induction_on with
  | zero => simp
  | of X => exact h X
  | neg X ih => simpa using φ.range.neg_mem ih
  | add x y hx hy => simpa using φ.range.add_mem hx hy

section map

variable {ℬ : Type*} [Category ℬ] [Abelian ℬ] (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- The homomorphism `K₀(𝒜) → K₀(ℬ)`, `[A] ↦ [F(A)]`, induced by an exact functor `F`. -/
noncomputable def map : KZero 𝒜 →+ KZero ℬ :=
  lift (fun X => mk ℬ (F.obj X)) fun _ hS => mk_of_shortExact _ (hS.map_of_exact F)

/-- The homomorphism induced by `F` sends `[X]` to `[F(X)]`. -/
@[simp]
theorem map_mk (X : 𝒜) : map F (mk 𝒜 X) = mk ℬ (F.obj X) :=
  lift_mk _ _ X

end map

section Serre

variable {C : Type*} [Category C] [Abelian C] (P : ObjectProperty C) [P.IsSerreClass]
  {D : Type*} [Category D] [Abelian D] (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

attribute [local instance] ObjectProperty.preservesFiniteLimits_ι
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass

/-- The map induced by the inclusion of `P` sends `[X]` to `[X.obj]`. -/
@[simp]
lemma map_ι_mk (X : P.FullSubcategory) : map P.ι (mk _ X) = mk C X.obj :=
  map_mk _ X

/-- If the cokernel of `f : X ⟶ Y` lies in `P`, then `[X] - ([ker f] + [Y])` comes from `K₀(P)`. -/
private lemma mk_sub_add_mem_range_map_ι {X Y : C} (f : X ⟶ Y) (hf : P (cokernel f)) :
    mk C X - (mk C (kernel f) + mk C Y) ∈ (map P.ι).range := by
  refine ⟨-mk _ ⟨cokernel f, hf⟩, ?_⟩
  rw [map_neg, map_ι_mk, mk_eq_kernel_add_image f, mk_eq_image_add_cokernel f]
  abel

/-- If `s` is an isomorphism modulo `P`, then `[X'] - [X]` comes from `K₀(P)`. -/
lemma mk_sub_mk_mem_range_map_ι {X' X : C} (s : X' ⟶ X) (hs : P.isoModSerre s) :
    mk C X' - mk C X ∈ (map P.ι).range := by
  convert (map P.ι).range.add_mem (mk_sub_add_mem_range_map_ι P s hs.2)
    ⟨mk _ ⟨kernel s, hs.1⟩, map_ι_mk P _⟩ using 1
  abel

include L in
/-- Objects of `C` which become isomorphic in the quotient `C/P` have classes differing by an
element coming from `K₀(P)`. -/
lemma mk_sub_mk_mem_range_map_ι_of_iso {X X' : C} (e : L.obj X ≅ L.obj X') :
    mk C X - mk C X' ∈ (map P.ι).range := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre e.hom
  have h₁ : L.map φ.f = L.map φ.s ≫ e.hom := by
    rw [hφ, φ.map_s_comp_map]
  have : IsIso (L.map φ.f) := by
    have := Localization.inverts L P.isoModSerre φ.s φ.hs
    rw [h₁]; infer_instance
  have hf : P.isoModSerre φ.f :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff L P φ.f).1 this
  have := (map P.ι).range.sub_mem (mk_sub_mk_mem_range_map_ι P φ.f hf)
    (mk_sub_mk_mem_range_map_ι P φ.s φ.hs)
  convert this using 1
  abel

variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]

include L in
/-- The composite `K₀(P) → K₀(C) → K₀(C/P)` vanishes, as objects of `P` are zero in `C/P`. -/
lemma map_comp_map_ι_eq_zero : (map L).comp (map P.ι) = 0 :=
  hom_ext fun X => by
    simpa using mk_eq_zero_of_isZero
      ((ObjectProperty.SerreClassLocalization.isZero_obj_iff L P X.obj).2 X.2)

include P in
/-- **Stacks 02MX, part (1), surjectivity.** The quotient functor `L : C ⥤ C/P` induces a
surjection `K₀(C) → K₀(C/P)`. -/
@[stacks 02MX "part (1): `K₀(C) → K₀(C/P)` is surjective"]
theorem surjective_map_localization : Function.Surjective (map L) := by
  have := Localization.essSurj L P.isoModSerre
  exact surjective_of_mk_mem_range _ fun Y =>
    ⟨mk C (L.objPreimage Y), by rw [map_mk]; exact mk_eq_of_iso (L.objObjPreimageIso Y)⟩

/-- A short exact sequence in `C/P` lifts, up to isomorphism, to objects of `C` whose classes
satisfy the additivity relation modulo the image of `K₀(P)`. -/
lemma exists_mk_sub_mem_range_map_ι (S : ShortComplex D) (hS : S.ShortExact) :
    ∃ (X₁ X₂ X₃ : C) (_ : L.obj X₁ ≅ S.X₁) (_ : L.obj X₂ ≅ S.X₂) (_ : L.obj X₃ ≅ S.X₃),
      mk C X₂ - (mk C X₁ + mk C X₃) ∈ (map P.ι).range := by
  obtain ⟨a, ⟨e⟩⟩ := (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk S.g)
  let eL : L.obj a.left ≅ S.X₂ := Arrow.leftFunc.mapIso e
  let eR : L.obj a.right ≅ S.X₃ := Arrow.rightFunc.mapIso e
  have hu : L.map a.hom = eL.hom ≫ S.g ≫ eR.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact (Arrow.w e.hom).symm
  have : Epi (L.map a.hom) := by
    have := hS.epi_g
    rw [hu]
    infer_instance
  have hc : P (cokernel a.hom) := (ObjectProperty.SerreClassLocalization.isZero_obj_iff L P _).1
    (IsZero.of_iso (isZero_cokernel_of_epi _) (PreservesCokernel.iso L a.hom))
  refine ⟨kernel a.hom, a.left, a.right, PreservesKernel.iso L a.hom ≪≫ kernelIsoOfEq hu ≪≫
    kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _ ≪≫
    (limit.isLimit _).conePointUniqueUpToIso hS.fIsKernel, eL, eR, ?_⟩
  exact mk_sub_add_mem_range_map_ι P a.hom hc

include P in
/-- **Stacks 02MX, part (1), exactness in the middle.** The sequence
`K₀(P) → K₀(C) → K₀(C/P)` induced by the inclusion of `P` and the quotient functor is exact. -/
@[stacks 02MX "part (1): exactness at `K₀(C)`"]
theorem exact_map_ι_map_localization : Function.Exact (map P.ι) (map L) := by
  have := Localization.essSurj L P.isoModSerre
  let R := (map P.ι).range
  let g : D → KZero C ⧸ R := fun Y => QuotientAddGroup.mk (mk C (L.objPreimage Y))
  have hg : ∀ (X : C) (Y : D), (L.obj X ≅ Y) → g Y = QuotientAddGroup.mk (mk C X) := fun X Y e =>
    QuotientAddGroup.eq_iff_sub_mem.2
      (mk_sub_mk_mem_range_map_ι_of_iso P L (L.objObjPreimageIso Y ≪≫ e.symm))
  have hS : ∀ S : ShortComplex D, S.ShortExact → g S.X₂ = g S.X₁ + g S.X₃ := fun S hS => by
    obtain ⟨X₁, X₂, X₃, e₁, e₂, e₃, h⟩ := exists_mk_sub_mem_range_map_ι P L S hS
    rwa [hg _ _ e₁, hg _ _ e₂, hg _ _ e₃, ← QuotientAddGroup.mk_add,
      QuotientAddGroup.eq_iff_sub_mem]
  let Ψ := KZero.lift g hS
  have hΨ : Ψ.comp (map L) = QuotientAddGroup.mk' R :=
    hom_ext fun X => by simpa [Ψ] using hg X _ (Iso.refl _)
  refine fun y => ⟨fun hy => ?_, ?_⟩
  · have := DFunLike.congr_fun hΨ y
    simp only [AddMonoidHom.comp_apply, hy, map_zero, QuotientAddGroup.mk'_apply] at this
    exact (QuotientAddGroup.eq_zero_iff y).1 this.symm
  · rintro ⟨x, rfl⟩
    exact DFunLike.congr_fun (map_comp_map_ι_eq_zero P L) x

end Serre

section Complexes

variable {C : Type*} [Category C] [Abelian C]

/-- For endomorphisms `φ, ψ` of `M` with `φ ∘ ψ = 0 = ψ ∘ φ`, the two homology objects
`H⁰ = Ker(φ)/Im(ψ)` and `H¹ = Ker(ψ)/Im(φ)` have the same class in `K₀`. -/
theorem mk_homology_eq_mk_homology {M : C} (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) :
    mk C (ShortComplex.mk ψ φ hψφ).homology = mk C (ShortComplex.mk φ ψ hφψ).homology := by
  have h₀ := mk_homology_add_mk_X₁ (ShortComplex.mk ψ φ hψφ)
  have h₁ := mk_homology_add_mk_X₁ (ShortComplex.mk φ ψ hφψ)
  dsimp only at h₀ h₁
  rw [add_comm (mk C (kernel ψ))] at h₀
  exact add_right_cancel (h₀.trans h₁.symm)

/-- The biproduct of a list of objects. -/
private noncomputable def listBiprod : List C → C
  | [] => 0
  | X :: l => X ⊞ listBiprod l

private lemma listBiprod_append (l l' : List C) :
    Nonempty (listBiprod (l ++ l') ≅ listBiprod l ⊞ listBiprod l') := by
  induction l with
  | nil => exact ⟨isoZeroBiprod (isZero_zero C)⟩
  | cons X l ih =>
    obtain ⟨e⟩ := ih
    exact ⟨biprod.mapIso (Iso.refl X) e ≪≫ (biprod.associator _ _ _).symm⟩

private lemma listBiprod_perm {l l' : List C} (h : l.Perm l') :
    Nonempty (listBiprod l ≅ listBiprod l') := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons X _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨biprod.mapIso (Iso.refl X) e⟩
  | swap x y l =>
    exact ⟨(biprod.associator _ _ _).symm ≪≫ biprod.mapIso (biprod.braiding y x) (Iso.refl _) ≪≫
      biprod.associator _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨e₁ ≪≫ e₂⟩

private lemma perm_of_sum_eq {α : Type*} {l l' : List α}
    (h : (l.map FreeAbelianGroup.of).sum = (l'.map FreeAbelianGroup.of).sum) : l.Perm l' := by
  classical
  have key : ∀ (a : α) (l : List α),
      FreeAbelianGroup.coeff a (l.map FreeAbelianGroup.of).sum = l.count a := by
    intro a l
    induction l with
    | nil => simp
    | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, map_add, ih, List.count_cons]
      simp [FreeAbelianGroup.coeff, Finsupp.single_apply, beq_iff_eq, add_comm]
  rw [List.perm_iff_count]
  intro a
  have := congrArg (FreeAbelianGroup.coeff a) h
  rw [key, key] at this
  exact_mod_cast this

variable (P : ObjectProperty C) [P.IsSerreClass]

private lemma mk_eq_zero_of_isZero_obj {X : P.FullSubcategory} (h : IsZero X.obj) :
    mk _ X = 0 :=
  mk_eq_zero_of_isZero (by rw [IsZero.iff_id_eq_zero]; ext; exact h.eq_of_src _ _)

/-- Isomorphic objects of `P` have the same class in `K₀(P)`. -/
private lemma mk_eq_of_iso_prop {X Y : C} (e : X ≅ Y) (hX : P X) (hY : P Y) :
    mk P.FullSubcategory ⟨X, hX⟩ = mk _ ⟨Y, hY⟩ :=
  mk_eq_of_iso (P.isoMk (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) e)

/-- A split short exact sequence in `C` whose outer terms lie in `P` has its middle term in `P`,
and gives the additivity relation in `K₀(P)`. -/
private lemma exists_prop_mk_eq_add {S : ShortComplex C} (s : S.Splitting) (h₁ : P S.X₁)
    (h₃ : P S.X₃) : ∃ h₂ : P S.X₂,
      mk P.FullSubcategory ⟨S.X₂, h₂⟩ = mk _ ⟨S.X₁, h₁⟩ + mk _ ⟨S.X₃, h₃⟩ := by
  have h₂ := P.prop_X₂_of_exact s.exact h₁ h₃
  refine ⟨h₂, mk_of_splitting (S := ShortComplex.mk
    (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : P.FullSubcategory) ⟶ ⟨S.X₂, h₂⟩)
    (ObjectProperty.homMk S.g : _ ⟶ (⟨S.X₃, h₃⟩ : P.FullSubcategory)) (by ext; exact S.zero))
    { r := ObjectProperty.homMk s.r
      s := ObjectProperty.homMk s.s
      f_r := by ext; exact s.f_r
      s_g := by ext; exact s.s_g
      id := by ext; exact s.id }⟩

/-- The homology of a direct sum of two short complexes, in `K₀(P)`. -/
private lemma exists_prop_homology_biprod (S S' : ShortComplex C) (h : P S.homology)
    (h' : P S'.homology) :
    ∃ h₂ : P (ShortComplex.mk (biprod.map S.f S'.f) (biprod.map S.g S'.g)
        (by ext <;> simp)).homology,
      mk P.FullSubcategory ⟨_, h₂⟩ = mk _ ⟨S.homology, h⟩ + mk _ ⟨S'.homology, h'⟩ := by
  let T := ShortComplex.mk (biprod.map S.f S'.f) (biprod.map S.g S'.g) (by ext <;> simp)
  let i₁ : S ⟶ T := ⟨biprod.inl, biprod.inl, biprod.inl, by simp [T], by simp [T]⟩
  let i₂ : S' ⟶ T := ⟨biprod.inr, biprod.inr, biprod.inr, by simp [T], by simp [T]⟩
  let p₁ : T ⟶ S := ⟨biprod.fst, biprod.fst, biprod.fst, by simp [T], by simp [T]⟩
  let p₂ : T ⟶ S' := ⟨biprod.snd, biprod.snd, biprod.snd, by simp [T], by simp [T]⟩
  have h₁ : i₁ ≫ p₁ = 𝟙 _ := by ext <;> simp [i₁, p₁]
  have h₂ : i₂ ≫ p₂ = 𝟙 _ := by ext <;> simp [i₂, p₂]
  have h₃ : i₁ ≫ p₂ = 0 := by ext <;> simp [i₁, p₂]
  have h₄ : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 _ := by ext <;> simp [i₁, i₂, p₁, p₂, T]
  exact exists_prop_mk_eq_add P (S := ShortComplex.mk (ShortComplex.homologyMap i₁)
    (ShortComplex.homologyMap p₂)
    (by rw [← ShortComplex.homologyMap_comp, h₃, ShortComplex.homologyMap_zero]))
    { r := ShortComplex.homologyMap p₁
      s := ShortComplex.homologyMap i₂
      f_r := by dsimp; rw [← ShortComplex.homologyMap_comp, h₁, ShortComplex.homologyMap_id]
      s_g := by dsimp; rw [← ShortComplex.homologyMap_comp, h₂, ShortComplex.homologyMap_id]
      id := by
        dsimp
        rw [← ShortComplex.homologyMap_comp p₁ i₁, ← ShortComplex.homologyMap_comp p₂ i₂,
          ← ShortComplex.homologyMap_add, h₄, ShortComplex.homologyMap_id] } h h'

/-- The pairs `(∑ l - ∑ l', [H⁰] - [H¹])` attached to a two-periodic complex
`M ⇄ N` with homology in `P`, where `M` and `N` are the biproducts of the lists `l` and `l'`. -/
private noncomputable def realizable :
    AddSubgroup (FreeAbelianGroup C × KZero P.FullSubcategory) where
  carrier := {z | ∃ (M N : C) (φ : M ⟶ N) (ψ : N ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0)
      (h₀ : P (ShortComplex.mk ψ φ hψφ).homology) (h₁ : P (ShortComplex.mk φ ψ hφψ).homology)
      (l l' : List C), Nonempty (M ≅ listBiprod l) ∧ Nonempty (N ≅ listBiprod l') ∧
      z = ((l.map FreeAbelianGroup.of).sum - (l'.map FreeAbelianGroup.of).sum,
        mk _ ⟨_, h₀⟩ - mk _ ⟨_, h₁⟩)}
  zero_mem' := by
    have h : P (ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) comp_zero).homology :=
      P.prop_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_zero C))
    exact ⟨0, 0, 0, 0, comp_zero, comp_zero, h, h, [], [], ⟨Iso.refl _⟩, ⟨Iso.refl _⟩,
      by ext <;> simp⟩
  neg_mem' := by
    rintro z ⟨M, N, φ, ψ, hφψ, hψφ, h₀, h₁, l, l', e, e', rfl⟩
    exact ⟨N, M, ψ, φ, hψφ, hφψ, h₁, h₀, l', l, e', e, by simp⟩
  add_mem' := by
    rintro z z' ⟨M, N, φ, ψ, hφψ, hψφ, h₀, h₁, l, l', ⟨e⟩, ⟨e'⟩, rfl⟩
      ⟨M₂, N₂, φ₂, ψ₂, hφψ₂, hψφ₂, h₀₂, h₁₂, l₂, l₂', ⟨e₂⟩, ⟨e₂'⟩, rfl⟩
    obtain ⟨H₀, hH₀⟩ := exists_prop_homology_biprod P _ _ h₀ h₀₂
    obtain ⟨H₁, hH₁⟩ := exists_prop_homology_biprod P _ _ h₁ h₁₂
    obtain ⟨a⟩ := listBiprod_append l l₂
    obtain ⟨a'⟩ := listBiprod_append l' l₂'
    refine ⟨M ⊞ M₂, N ⊞ N₂, biprod.map φ φ₂, biprod.map ψ ψ₂, by ext <;> simp [hφψ, hφψ₂],
      by ext <;> simp [hψφ, hψφ₂], H₀, H₁, l ++ l₂, l' ++ l₂', ⟨biprod.mapIso e e₂ ≪≫ a.symm⟩,
      ⟨biprod.mapIso e' e₂' ≪≫ a'.symm⟩, ?_⟩
    simp only [Prod.mk_add_mk, List.map_append, List.sum_append]
    dsimp only at hH₀ hH₁
    rw [hH₀, hH₁]
    ext <;> dsimp <;> abel

/-- The class of an object of `P` is realizable, by the complex `X ⇄ 0`. -/
private lemma mem_realizable_of (Y : P.FullSubcategory) :
    (FreeAbelianGroup.of Y.obj, mk _ Y) ∈ realizable P := by
  let e := (ShortComplex.HomologyData.ofZeros
    (ShortComplex.mk (0 : (0 : C) ⟶ Y.obj) (0 : Y.obj ⟶ 0) comp_zero) rfl rfl).left.homologyIso
  have h₀ : P (ShortComplex.mk (0 : (0 : C) ⟶ Y.obj) (0 : Y.obj ⟶ 0) comp_zero).homology :=
    P.prop_of_iso e.symm Y.2
  have hZ := ShortComplex.isZero_homology_of_isZero_X₂
    (ShortComplex.mk (0 : Y.obj ⟶ 0) (0 : (0 : C) ⟶ Y.obj) comp_zero) (isZero_zero C)
  refine ⟨Y.obj, 0, 0, 0, comp_zero, comp_zero, h₀, P.prop_of_isZero hZ, [Y.obj], [],
    ⟨isoBiprodZero (isZero_zero C)⟩, ⟨Iso.refl _⟩, ?_⟩
  rw [mk_eq_zero_of_isZero_obj P (X := ⟨_, P.prop_of_isZero hZ⟩) hZ,
    mk_eq_of_iso_prop P e h₀ Y.2]
  simp

/-- For an exact short complex `S`, the complex `X₁ ⊞ X₃ → X₂ → X₁ ⊞ X₃` is exact at `X₂`. -/
private lemma exact_fst_comp_f_g_comp_inr {S : ShortComplex C} (hS : S.Exact) :
    (ShortComplex.mk ((biprod.fst : S.X₁ ⊞ S.X₃ ⟶ _) ≫ S.f)
      (S.g ≫ (biprod.inr : _ ⟶ S.X₁ ⊞ S.X₃)) (by simp)).Exact := by
  let S₃ := ShortComplex.mk S.f (S.g ≫ (biprod.inr : _ ⟶ S.X₁ ⊞ S.X₃)) (by simp)
  let α : ShortComplex.mk ((biprod.fst : S.X₁ ⊞ S.X₃ ⟶ _) ≫ S.f)
      (S.g ≫ (biprod.inr : _ ⟶ S.X₁ ⊞ S.X₃)) (by simp) ⟶ S₃ :=
    ⟨biprod.fst, 𝟙 _, 𝟙 _, by simp [S₃], by simp [S₃]⟩
  let β : S ⟶ S₃ := ⟨𝟙 _, 𝟙 _, biprod.inr, by simp [S₃], by simp [S₃]⟩
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono β).1 hS)

/-- For a short exact sequence `S`, the complex `X₂ → X₁ ⊞ X₃ → X₂` is exact at `X₁ ⊞ X₃`. -/
private lemma exact_g_comp_inr_fst_comp_f {S : ShortComplex C} (hS : S.ShortExact) :
    (ShortComplex.mk (S.g ≫ (biprod.inr : _ ⟶ S.X₁ ⊞ S.X₃))
      ((biprod.fst : S.X₁ ⊞ S.X₃ ⟶ _) ≫ S.f) (by simp)).Exact := by
  have := hS.mono_f
  have := hS.epi_g
  let S₄ := ShortComplex.mk (biprod.inr : S.X₃ ⟶ S.X₁ ⊞ S.X₃) biprod.fst (by simp)
  have h₄ : S₄.Exact := ShortComplex.Splitting.exact
    { r := biprod.snd, s := biprod.inl, id := by dsimp [S₄]; rw [add_comm]; exact biprod.total }
  let S₅ := ShortComplex.mk (S.g ≫ biprod.inr) (biprod.fst : S.X₁ ⊞ S.X₃ ⟶ S.X₁) (by simp)
  let α : S₅ ⟶ S₄ := ⟨S.g, 𝟙 _, 𝟙 _, by simp [S₄, S₅], by simp [S₄, S₅]⟩
  let β : S₅ ⟶ ShortComplex.mk (S.g ≫ (biprod.inr : _ ⟶ S.X₁ ⊞ S.X₃))
      ((biprod.fst : S.X₁ ⊞ S.X₃ ⟶ _) ≫ S.f) (by simp) :=
    ⟨𝟙 _, 𝟙 _, S.f, by simp [S₅], by simp [S₅]⟩
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono β).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 h₄)

/-- The relation of a short exact sequence `0 → X₁ → X₂ → X₃ → 0` is realizable, by the exact
complex `X₂ ⇄ X₁ ⊞ X₃`. -/
private lemma mem_realizable_of_shortExact (S : ShortComplex C) (hS : S.ShortExact) :
    (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃, 0) ∈
      realizable P := by
  let φ : S.X₂ ⟶ S.X₁ ⊞ S.X₃ := S.g ≫ biprod.inr
  let ψ : S.X₁ ⊞ S.X₃ ⟶ S.X₂ := biprod.fst ≫ S.f
  have hφψ : φ ≫ ψ = 0 := by simp [φ, ψ]
  have hψφ : ψ ≫ φ = 0 := by simp [φ, ψ]
  have hex₀ : (ShortComplex.mk ψ φ hψφ).Exact := exact_fst_comp_f_g_comp_inr hS.exact
  have hex₁ : (ShortComplex.mk φ ψ hφψ).Exact := exact_g_comp_inr_fst_comp_f hS
  have hZ₀ := (ShortComplex.exact_iff_isZero_homology _).1 hex₀
  have hZ₁ := (ShortComplex.exact_iff_isZero_homology _).1 hex₁
  refine ⟨S.X₂, S.X₁ ⊞ S.X₃, φ, ψ, hφψ, hψφ, P.prop_of_isZero hZ₀, P.prop_of_isZero hZ₁,
    [S.X₂], [S.X₁, S.X₃], ⟨isoBiprodZero (isZero_zero C)⟩,
    ⟨biprod.mapIso (Iso.refl _) (isoBiprodZero (isZero_zero C))⟩, ?_⟩
  rw [mk_eq_zero_of_isZero_obj P (X := ⟨_, P.prop_of_isZero hZ₀⟩) hZ₀,
    mk_eq_zero_of_isZero_obj P (X := ⟨_, P.prop_of_isZero hZ₁⟩) hZ₁]
  ext
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    abel
  · simp

/-- Every element of the free abelian group on `P` is realizable together with its class. -/
private lemma mem_realizable_map (w : FreeAbelianGroup P.FullSubcategory) :
    (FreeAbelianGroup.map (fun Y : P.FullSubcategory => Y.obj) w,
      QuotientAddGroup.mk' (kZeroRelations _) w) ∈ realizable P := by
  induction w using FreeAbelianGroup.induction_on with
  | zero => rw [map_zero, map_zero]; exact (realizable P).zero_mem
  | of Y => exact mem_realizable_of P Y
  | neg Y ih => rw [map_neg, map_neg]; exact (realizable P).neg_mem ih
  | add w w' ih ih' => rw [map_add, map_add]; exact (realizable P).add_mem ih ih'

private lemma kZeroRelations_le_comap_inl :
    kZeroRelations C ≤ (realizable P).comap (AddMonoidHom.inl _ _) :=
  (AddSubgroup.closure_le _).2 fun _ ⟨S, hS, h⟩ => h ▸ mem_realizable_of_shortExact P S hS

attribute [local instance] ObjectProperty.preservesFiniteLimits_ι
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass

/-- **Stacks 02MX, part (2).** An element of `K₀(P)` dies in `K₀(C)` if and only if it is
`[H⁰(M, φ, ψ)] - [H¹(M, φ, ψ)]` for a complex `(M, φ, ψ)` (endomorphisms `φ, ψ` of an object `M`
of `C` with `φ ∘ ψ = 0 = ψ ∘ φ`) whose homology `H⁰ = Ker(φ)/Im(ψ)` and `H¹ = Ker(ψ)/Im(φ)`
lies in `P`, i.e. which becomes exact in `C/P`. -/
@[stacks 02MX "part (2)"]
theorem map_ι_eq_zero_iff (x : KZero P.FullSubcategory) :
    map P.ι x = 0 ↔ ∃ (M : C) (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0)
      (h₀ : P (ShortComplex.mk ψ φ hψφ).homology) (h₁ : P (ShortComplex.mk φ ψ hφψ).homology),
      x = mk _ ⟨_, h₀⟩ - mk _ ⟨_, h₁⟩ := by
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    let ι' := FreeAbelianGroup.map (fun Y : P.FullSubcategory => Y.obj)
    have hmap : (map P.ι).comp (QuotientAddGroup.mk' _) =
        (QuotientAddGroup.mk' (kZeroRelations C)).comp ι' :=
      FreeAbelianGroup.lift_ext _ _ fun Y => by
        simp only [AddMonoidHom.comp_apply, ι', FreeAbelianGroup.map_of_apply]
        exact map_mk P.ι Y
    have hw : ι' w ∈ kZeroRelations C := by
      have := DFunLike.congr_fun hmap w
      rw [AddMonoidHom.comp_apply, hx, AddMonoidHom.comp_apply] at this
      exact (QuotientAddGroup.eq_zero_iff _).1 this.symm
    obtain ⟨M, N, φ, ψ, hφψ, hψφ, h₀, h₁, l, l', ⟨e⟩, ⟨e'⟩, hz⟩ :=
      (realizable P).sub_mem (mem_realizable_map P w) (kZeroRelations_le_comap_inl P hw)
    simp only [ι', AddMonoidHom.inl_apply, Prod.mk_sub_mk, sub_self, sub_zero, Prod.mk.injEq] at hz
    obtain ⟨α⟩ := listBiprod_perm (perm_of_sum_eq (sub_eq_zero.1 hz.1.symm))
    let β : N ≅ M := e' ≪≫ α.symm ≪≫ e.symm
    let e₀ := ShortComplex.homologyMapIso (ShortComplex.isoMk β (Iso.refl M) β
      (S₁ := ShortComplex.mk ψ φ hψφ)
      (S₂ := ShortComplex.mk (β.inv ≫ ψ) (φ ≫ β.hom) (by simp [reassoc_of% hψφ]))
      (by simp) (by simp))
    let e₁ := ShortComplex.homologyMapIso (ShortComplex.isoMk (Iso.refl M) β (Iso.refl M)
      (S₁ := ShortComplex.mk φ ψ hφψ)
      (S₂ := ShortComplex.mk (φ ≫ β.hom) (β.inv ≫ ψ) (by simpa using hφψ))
      (by simp) (by simp))
    refine ⟨M, φ ≫ β.hom, β.inv ≫ ψ, by simpa using hφψ, by simp [reassoc_of% hψφ],
      P.prop_of_iso e₀ h₀, P.prop_of_iso e₁ h₁, ?_⟩
    rw [hz.2, mk_eq_of_iso_prop P e₀ h₀ _, mk_eq_of_iso_prop P e₁ h₁ _]
  · rintro ⟨M, φ, ψ, hφψ, hψφ, h₀, h₁, rfl⟩
    rw [map_sub, map_ι_mk, map_ι_mk, mk_homology_eq_mk_homology φ ψ hφψ hψφ, sub_self]

end Complexes

end KZero
