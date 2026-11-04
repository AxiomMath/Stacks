module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Localization

/-!
# Morphisms into filtered injective objects extend along strict morphisms

Let `𝒜` be an abelian category, `u : A ⟶ B` a strict morphism of filtered objects of `𝒜` and
`f : A ⟶ I` a morphism into a filtered injective object `I` of `Fil^f(𝒜)`. Then `f` extends
along `u`.

The source's route is followed: the pushout `I ⨿_A B` is formed in `Fil(𝒜)`, the map
`I ⟶ I ⨿_A B` is a strict monomorphism ([Stacks, Tag 05SM]), hence split by
`CategoryTheory.FilteredObject.isSplitMono_of_isFilteredInjective`, and the extension is
`B ⟶ I ⨿_A B ⟶ I`.

The filtration on the pushout is `F^p(I ⨿_A B) = Im(F^pI ⊕ F^pB)`, and the point of the proof is
that `Im(F^pI ⊕ F^pB)` is also the *kernel* of the map from `I ⨿_A B` to the pushout `D^p` of
`A/F^pA ⟶ B/F^pB` along `A/F^pA ⟶ I/F^pI`. Taking that kernel as the definition of the filtration
makes both the functoriality in `p` and the strictness computation formal: the composite
`I ⟶ I ⨿_A B ⟶ D^p` is `I ⟶ I/F^pI ⟶ D^p`, whose second factor is a monomorphism because it is
the pushout of the monomorphism `A/F^pA ⟶ B/F^pB` — and *that* map is a monomorphism precisely
because `u` is strict. Hence the pullback of `F^p(I ⨿_A B)` along `I ⟶ I ⨿_A B` is
`Ker(I ⟶ I/F^pI) = F^pI`, which is strictness of `I ⟶ I ⨿_A B`.

The object `I ⨿_A B` is built as `Limits.pushout f.hom u.hom` in `𝒜` equipped with the filtration
above, and is not shown to be a pushout in `Fil(𝒜)`: the argument needs only the commuting square
`u ≫ inr = f ≫ inl` together with the strictness of `inl`, and the splitting lemma applies to
`inl` because its *source* is `I`, whose filtration is finite and filtered injective. For the same
reason the identification `Ker(I ⨿_A B ⟶ D^p) = Im(F^pI ⊕ F^pB)` of the filtration with the
source's is motivation rather than a step: only the kernel description is used below.

Monomorphy of `u` is not assumed, although the source says *strict monomorphism*. Strictness of
`u` alone makes `A/F^pA ⟶ B/F^pB` a monomorphism (`mono_coquotMap`), since it says that `F^pA` is
the pullback of `F^pB` along `u` — in particular `Ker(u) ≤ F^pA` for every `p` — and that is the
only input the strictness of `I ⟶ I ⨿_A B` is computed from. The splitting lemma then consumes
strictness of `I ⟶ I ⨿_A B` alone, monomorphy being derivable there from the finiteness of the
filtration of `I`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredInjectiveExtension

namespace CategoryTheory.FilteredObject.Extension

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- In an abelian category, a monomorphism `ι : S ⟶ X` exhibits `S` as the pullback of the kernel
of `h : P ⟶ D` along `w : X ⟶ P`, as soon as `w ≫ h` factors through the cokernel of `ι` by a
monomorphism. -/
private lemma isPullback_kernel_ι {S X P D : 𝒜} (ι : S ⟶ X) [Mono ι] {h : P ⟶ D} (w : X ⟶ P)
    (n : cokernel ι ⟶ D) [Mono n] (hn : w ≫ h = cokernel.π ι ≫ n)
    (l : S ⟶ kernel h) (hl : l ≫ kernel.ι h = ι ≫ w) :
    IsPullback l ι (kernel.ι h) w := by
  have key : ∀ {T : 𝒜} (a : T ⟶ kernel h) (b : T ⟶ X), a ≫ kernel.ι h = b ≫ w →
      b ≫ cokernel.π ι = 0 := by
    intro T a b hab
    refine zero_of_comp_mono n ?_
    rw [Category.assoc, ← hn, ← Category.assoc, ← hab, Category.assoc, kernel.condition,
      comp_zero]
  refine IsPullback.of_isLimit' ⟨hl⟩ (PullbackCone.IsLimit.mk _
    (fun s => Abelian.monoLift ι s.snd (key s.fst s.snd s.condition)) (fun s => ?_)
    (fun s => Abelian.monoLift_comp _ _ _) (fun s m h₁ h₂ => ?_))
  · rw [← cancel_mono (kernel.ι h), Category.assoc, hl, ← Category.assoc,
      Abelian.monoLift_comp, s.condition]
  · rw [← cancel_mono ι, Abelian.monoLift_comp, h₂]

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {A B I : FilteredObject 𝒜 ℤᵒᵖ}

/-- The map `A/F^iA ⟶ B/F^iB` induced by a morphism `u : A ⟶ B` of filtered objects. -/
private noncomputable def coquotMap (u : A ⟶ B) (i : ℤᵒᵖ) :
    cokernel (A.filtration.ι.app i) ⟶ cokernel (B.filtration.ι.app i) :=
  cokernel.desc _ (u.hom ≫ cokernel.π _) (by rw [← Hom.comm_assoc]; simp)

@[reassoc]
private lemma π_coquotMap (u : A ⟶ B) (i : ℤᵒᵖ) :
    cokernel.π (A.filtration.ι.app i) ≫ coquotMap u i =
      u.hom ≫ cokernel.π (B.filtration.ι.app i) :=
  cokernel.π_desc _ _ _

private lemma filtration_ι_comp_π (X : FilteredObject 𝒜 ℤᵒᵖ) {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    X.filtration.ι.app i ≫ cokernel.π (X.filtration.ι.app j) = 0 := by
  rw [← X.filtration.diagram_map_comp_ι_app φ, Category.assoc, cokernel.condition, comp_zero]

/-- The map `X/F^iX ⟶ X/F^jX` for `j ≤ i`. -/
private noncomputable def coquotRes (X : FilteredObject 𝒜 ℤᵒᵖ) {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    cokernel (X.filtration.ι.app i) ⟶ cokernel (X.filtration.ι.app j) :=
  cokernel.desc _ (cokernel.π _) (filtration_ι_comp_π X φ)

@[reassoc]
private lemma π_coquotRes (X : FilteredObject 𝒜 ℤᵒᵖ) {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    cokernel.π (X.filtration.ι.app i) ≫ coquotRes X φ = cokernel.π (X.filtration.ι.app j) :=
  cokernel.π_desc _ _ _

attribute [local simp] π_coquotMap π_coquotMap_assoc π_coquotRes π_coquotRes_assoc

private lemma coquotMap_coquotRes (u : A ⟶ B) {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    coquotMap u i ≫ coquotRes B φ = coquotRes A φ ≫ coquotMap u j := by
  rw [← cancel_epi (cokernel.π (A.filtration.ι.app i))]
  simp

/-- Strictness of `u : A ⟶ B` says that `F^iA` is the pullback of `F^iB` along `u`, so the
induced map `A/F^iA ⟶ B/F^iB` on quotients is a monomorphism. -/
private lemma mono_coquotMap (u : A ⟶ B) [IsStrictHom u] (i : ℤᵒᵖ) : Mono (coquotMap u i) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T t ht
  have hepi : Epi (pullback.fst t (cokernel.π (A.filtration.ι.app i))) := inferInstance
  have hcond : pullback.fst t (cokernel.π (A.filtration.ι.app i)) ≫ t =
      pullback.snd t (cokernel.π (A.filtration.ι.app i)) ≫
        cokernel.π (A.filtration.ι.app i) := pullback.condition
  have h1 : (pullback.snd t (cokernel.π (A.filtration.ι.app i)) ≫ u.hom) ≫
      cokernel.π (B.filtration.ι.app i) = 0 := by
    rw [Category.assoc, ← π_coquotMap u i, ← Category.assoc, ← hcond, Category.assoc, ht,
      comp_zero]
  have hw := Abelian.monoLift_comp (B.filtration.ι.app i) _ h1
  have hl := (IsStrictHom.isPullback u i).lift_snd
    (Abelian.monoLift (B.filtration.ι.app i) _ h1)
    (pullback.snd t (cokernel.π (A.filtration.ι.app i))) hw
  rw [← cancel_epi (pullback.fst t (cokernel.π (A.filtration.ι.app i))), comp_zero, hcond, ← hl,
    Category.assoc, cokernel.condition, comp_zero]

variable (f : A ⟶ I) (u : A ⟶ B)

/-- The pushout `D^i` of `A/F^iA ⟶ I/F^iI` and `A/F^iA ⟶ B/F^iB`. The pushout `I ⨿_A B` maps to
it, and the kernel of that map is `Im(F^iI ⊕ F^iB)`, the `i`-th step of the filtration of
`I ⨿_A B`. -/
private noncomputable abbrev quotPushout (i : ℤᵒᵖ) : 𝒜 :=
  pushout (coquotMap f i) (coquotMap u i)

/-- The map `I ⨿_A B ⟶ D^i` whose kernel is the `i`-th filtration step of `I ⨿_A B`. -/
private noncomputable def toQuotPushout (i : ℤᵒᵖ) :
    pushout f.hom u.hom ⟶ quotPushout f u i :=
  pushout.desc (cokernel.π _ ≫ pushout.inl _ _) (cokernel.π _ ≫ pushout.inr _ _) (by
    rw [← Category.assoc, ← Category.assoc, ← π_coquotMap f i, ← π_coquotMap u i, Category.assoc,
      Category.assoc, pushout.condition])

@[reassoc]
private lemma inl_toQuotPushout (i : ℤᵒᵖ) :
    pushout.inl f.hom u.hom ≫ toQuotPushout f u i =
      cokernel.π (I.filtration.ι.app i) ≫ pushout.inl (coquotMap f i) (coquotMap u i) :=
  pushout.inl_desc _ _ _

@[reassoc]
private lemma inr_toQuotPushout (i : ℤᵒᵖ) :
    pushout.inr f.hom u.hom ≫ toQuotPushout f u i =
      cokernel.π (B.filtration.ι.app i) ≫ pushout.inr (coquotMap f i) (coquotMap u i) :=
  pushout.inr_desc _ _ _

/-- The map `D^i ⟶ D^j` for `j ≤ i`. -/
private noncomputable def quotPushoutRes {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    quotPushout f u i ⟶ quotPushout f u j :=
  pushout.desc (coquotRes I φ ≫ pushout.inl _ _) (coquotRes B φ ≫ pushout.inr _ _) (by
    rw [← Category.assoc, ← Category.assoc, coquotMap_coquotRes f φ, coquotMap_coquotRes u φ,
      Category.assoc, Category.assoc, pushout.condition])

@[reassoc]
private lemma inl_quotPushoutRes {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    pushout.inl (coquotMap f i) (coquotMap u i) ≫ quotPushoutRes f u φ =
      coquotRes I φ ≫ pushout.inl (coquotMap f j) (coquotMap u j) :=
  pushout.inl_desc _ _ _

@[reassoc]
private lemma inr_quotPushoutRes {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    pushout.inr (coquotMap f i) (coquotMap u i) ≫ quotPushoutRes f u φ =
      coquotRes B φ ≫ pushout.inr (coquotMap f j) (coquotMap u j) :=
  pushout.inr_desc _ _ _

attribute [local simp] inl_toQuotPushout inl_toQuotPushout_assoc inr_toQuotPushout
  inr_toQuotPushout_assoc inl_quotPushoutRes inl_quotPushoutRes_assoc inr_quotPushoutRes
  inr_quotPushoutRes_assoc

private lemma toQuotPushout_res {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    toQuotPushout f u i ≫ quotPushoutRes f u φ = toQuotPushout f u j := by
  apply pushout.hom_ext <;> simp

/-- The map `Ker(I ⨿_A B ⟶ D^i) ⟶ Ker(I ⨿_A B ⟶ D^j)` for `j ≤ i`. -/
private noncomputable def pushoutFiltrationMap {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    kernel (toQuotPushout f u i) ⟶ kernel (toQuotPushout f u j) :=
  kernel.lift _ (kernel.ι (toQuotPushout f u i)) (by
    rw [← toQuotPushout_res f u φ, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc]
private lemma pushoutFiltrationMap_ι {i j : ℤᵒᵖ} (φ : i ⟶ j) :
    pushoutFiltrationMap f u φ ≫ kernel.ι (toQuotPushout f u j) =
      kernel.ι (toQuotPushout f u i) :=
  kernel.lift_ι _ _ _

attribute [local simp] toQuotPushout_res pushoutFiltrationMap_ι pushoutFiltrationMap_ι_assoc

/-- The filtration on `I ⨿_A B`: the `i`-th step is `Ker(I ⨿_A B ⟶ D^i) = Im(F^iI ⊕ F^iB)`. -/
private noncomputable def pushoutFiltration : Filtration (pushout f.hom u.hom) ℤᵒᵖ where
  toMonoOver :=
    { obj := fun i => MonoOver.mk (kernel.ι (toQuotPushout f u i))
      map := fun {i j} φ => MonoOver.homMk (pushoutFiltrationMap f u φ) (by simp)
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }

/-- The filtered object `I ⨿_A B`. -/
private noncomputable abbrev pushoutObj : FilteredObject 𝒜 ℤᵒᵖ :=
  ⟨pushout f.hom u.hom, pushoutFiltration f u⟩

/-- The map `I ⟶ I ⨿_A B`. -/
private noncomputable def pushoutInl : I ⟶ pushoutObj f u :=
  homMk (pushout.inl f.hom u.hom)
    (fun i => kernel.lift _ (I.filtration.ι.app i ≫ pushout.inl f.hom u.hom) (by simp))
    (fun i => kernel.lift_ι _ _ _)

private lemma pushoutInl_hom : (pushoutInl f u).hom = pushout.inl f.hom u.hom := rfl

/-- The map `B ⟶ I ⨿_A B`. -/
private noncomputable def pushoutInr : B ⟶ pushoutObj f u :=
  homMk (pushout.inr f.hom u.hom)
    (fun i => kernel.lift _ (B.filtration.ι.app i ≫ pushout.inr f.hom u.hom) (by simp))
    (fun i => kernel.lift_ι _ _ _)

private lemma pushoutInr_hom : (pushoutInr f u).hom = pushout.inr f.hom u.hom := rfl

attribute [local simp] pushoutInl_hom pushoutInr_hom

private lemma pushout_comm : u ≫ pushoutInr f u = f ≫ pushoutInl f u := by
  apply FilteredObject.hom_ext
  simpa using pushout.condition.symm

/-- The pushout of a strict monomorphism is strict: `I ⟶ I ⨿_A B` is strict because the pullback
of `Ker(I ⨿_A B ⟶ D^i)` along it is `Ker(I ⟶ I/F^iI) = F^iI`, the map `I/F^iI ⟶ D^i` being a
monomorphism. -/
private lemma isStrictHom_pushoutInl [IsStrictHom u] : IsStrictHom (pushoutInl f u) where
  isPullback i := by
    have := mono_coquotMap u i
    have hmono : Mono (pushout.inl (coquotMap f i) (coquotMap u i)) :=
      Abelian.mono_pushout_of_mono_g _ _
    exact isPullback_kernel_ι (I.filtration.ι.app i) (pushout.inl f.hom u.hom)
      (pushout.inl (coquotMap f i) (coquotMap u i)) (inl_toQuotPushout f u i) _
      ((pushoutInl f u).comm i)

end

end CategoryTheory.FilteredObject.Extension

namespace CategoryTheory.FilteredObject

open Extension in
/-- **Stacks 05TR.** Let `𝒜` be an abelian category, let `u : A ⟶ B` be a strict morphism of
filtered objects of `𝒜` and let `f : A ⟶ I` be a morphism into a filtered injective object `I` of
`Fil^f(𝒜)`: its filtration is finite and every graded piece `gr^p(I) = F^p I / F^{p + 1} I` is an
injective object of `𝒜`. Then `f` extends along `u`: there is a morphism `g : B ⟶ I` of filtered
objects with `f = u ≫ g`. The source assumes `u` to be a strict monomorphism; monomorphy is not
used, and is automatic on `Fil^f(𝒜)`. -/
@[stacks 05TR]
public theorem factors_of_isFilteredInjective {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B I : FilteredObject 𝒜 ℤᵒᵖ} (f : A ⟶ I) (u : A ⟶ B) [IsStrictHom u]
    (hI : I.IsFilteredInjective) :
    ∃ g : B ⟶ I, u ≫ g = f := by
  have := isStrictHom_pushoutInl f u
  have hsplit := isSplitMono_of_isFilteredInjective (pushoutInl f u) hI
  refine ⟨pushoutInr f u ≫ retraction (pushoutInl f u), ?_⟩
  rw [← Category.assoc, pushout_comm f u, Category.assoc, IsSplitMono.id, Category.comp_id]

end CategoryTheory.FilteredObject

end FilteredInjectiveExtension

end
