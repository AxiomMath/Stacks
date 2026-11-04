module

public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compactness passes along surjections of sheaves of sets

A sheaf of sets `F` on a site is quasi-compact when every surjection `∐_{i ∈ I} G_i ⟶ F` restricts
to a surjection from the coproduct over a finite subset of `I`. If `φ : F ⟶ G` is a surjection of
sheaves of sets and `F` is quasi-compact, then `G` is quasi-compact. In particular, if a morphism
`U ⟶ V` of the site induces a surjection `h_U^# ⟶ h_V^#` of sheafified representables and `h_U^#`
is quasi-compact, then so is `h_V^#`.

## Main results

* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff`: a family of morphisms of sheaves of
  sets induces a surjection out of the coproduct exactly when every section of the target lies,
  locally, in the image of a single member of the family.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_comp`: a jointly surjective family
  composed with a jointly surjective family over each of its sources is jointly surjective.
* `CategoryTheory.Sheaf.exists_pullback_section`: two sections of `H` and of `F` over `V` with the
  same image in `G` come from a section of `H ×_G F` over `V`.
* `CategoryTheory.Sheaf.isQuasiCompact_of_isLocallySurjective`: quasi-compactness of a sheaf of
  sets passes along a surjection.
* `CategoryTheory.Sheaf.isQuasiCompact_sheafifiedYoneda_of_isLocallySurjective`: if
  `h_U^# ⟶ h_V^#` is a surjection and `h_U^#` is quasi-compact, then so is `h_V^#`.

## References

* [Stacks Project, Tag 0GMP](https://stacks.math.columbia.edu/tag/0GMP)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Surjections out of a coproduct of sheaves of sets -/

/-- A morphism of sheaves of sets that a surjection factors through is itself a surjection. -/
public lemma isLocallySurjective_of_fac {F₁ F₂ F₃ : Sheaf J (Type max u v)} {f₁ : F₁ ⟶ F₂}
    {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃) [IsLocallySurjective f₃] :
    IsLocallySurjective f₂ := by
  refine Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (f₁ := f₁.hom) (f₃ := f₃.hom) ?_
  rw [← ObjectProperty.FullSubcategory.comp_hom, fac]

/-- Precomposing a map out of a coproduct of sheaves of sets with `p` acts componentwise. -/
private theorem sigmaDesc_comp {I : Type max u v} {G : I → Sheaf J (Type max u v)}
    {F F' : Sheaf J (Type max u v)} (g : ∀ i, G i ⟶ F) (p : F ⟶ F') :
    Sigma.desc g ≫ p = Sigma.desc fun i ↦ g i ≫ p :=
  Sigma.hom_ext _ _ fun i ↦ by rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc]

/-- If every member of a family of morphisms of sheaves of sets factors through a common
`p : F' ⟶ F`, and the family induces a surjection `∐_{i ∈ I} G_i ⟶ F`, then `p` is a surjection. -/
public lemma isLocallySurjective_of_sigmaDesc_fac {I : Type max u v}
    {G : I → Sheaf J (Type max u v)} {F F' : Sheaf J (Type max u v)} {f : ∀ i, G i ⟶ F}
    (hf : IsLocallySurjective (Sigma.desc f)) {p : F' ⟶ F} (g : ∀ i, G i ⟶ F')
    (fac : ∀ i, g i ≫ p = f i) :
    IsLocallySurjective p := by
  exact isLocallySurjective_of_fac (f₁ := Sigma.desc g) (f₃ := Sigma.desc f)
    (by simp only [sigmaDesc_comp, fac])

/-- Let `(f_i : G_i ⟶ F)_{i ∈ I}` induce a surjection
`∐_{i ∈ I} G_i ⟶ F` of sheaves of sets and let `T` be a subpresheaf of `F` containing the image of
every `f_i`. Then `T` contains every section of `F` locally, i.e. `T^# = ⊤`. -/
public lemma sheafify_eq_top_of_range_le {I : Type max u v} {G : I → Sheaf J (Type max u v)}
    {F : Sheaf J (Type max u v)} {f : ∀ i, G i ⟶ F}
    (hf : IsLocallySurjective (Sigma.desc f)) (T : Subfunctor F.obj)
    (hT : ∀ i, Subfunctor.range (f i).hom ≤ T) :
    T.sheafify J = ⊤ := by
  have hF : Presieve.IsSheaf J F.obj := (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property
  have hle : ∀ i, Subfunctor.range (f i).hom ≤ T.sheafify J :=
    fun i ↦ (hT i).trans (T.le_sheafify J)
  have : Presheaf.IsLocallySurjective J (T.sheafify J).ι :=
    isLocallySurjective_of_sigmaDesc_fac
      (F' := (⟨(T.sheafify J).toFunctor,
        (isSheaf_iff_isSheaf_of_type J _).2 (T.sheafify_isSheaf hF)⟩ : Sheaf J (Type max u v)))
      (p := ObjectProperty.homMk (T.sheafify J).ι) hf
      (fun i ↦ ObjectProperty.homMk (Subfunctor.lift (f i).hom (hle i)))
      (fun i ↦ Sheaf.hom_ext (Subfunctor.lift_ι (f i).hom (hle i)))
  have h := (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' J
    (T.sheafify J).ι).1 inferInstance
  rwa [Subfunctor.range_ι, T.sheafify_sheafify hF] at h

/-- A family `(f_i : G_i ⟶ F)_{i ∈ I}` of morphisms of sheaves
of sets induces a surjection `∐_{i ∈ I} G_i ⟶ F` if and only if every section of `F` lies, locally,
in the image of a single `f_i`. -/
@[sga "3 IV 4.4.8" "(v), (vi)"]
theorem isLocallySurjective_sigmaDesc_iff {I : Type max u v} {G : I → Sheaf J (Type max u v)}
    {F : Sheaf J (Type max u v)} (f : ∀ i, G i ⟶ F) :
    IsLocallySurjective (Sigma.desc f) ↔
      ∀ ⦃U : C⦄ (s : F.obj.obj (op U)),
        ∃ T : Sieve U, T ∈ J U ∧
          ∀ ⦃V : C⦄ (g : V ⟶ U), T g →
            ∃ (i : I) (t : (G i).obj.obj (op V)),
              (f i).hom.app (op V) t = F.obj.map g.op s := by
  constructor
  · intro hf U s
    refine ⟨(⨆ i, Subfunctor.range (f i).hom).sieveOfSection s, ?_, ?_⟩
    · have hs : s ∈ ((⨆ i, Subfunctor.range (f i).hom).sheafify J).obj (op U) := by
        rw [sheafify_eq_top_of_range_le hf (⨆ i, Subfunctor.range (f i).hom)
          (le_iSup fun i ↦ Subfunctor.range (f i).hom)]
        simp
      exact hs
    · intro V g hg
      have hg' : F.obj.map g.op s ∈ (⨆ i, Subfunctor.range (f i).hom).obj (op V) := hg
      rw [Subfunctor.iSup_obj] at hg'
      exact Set.mem_iUnion.1 hg'
  · refine fun hf ↦ ⟨fun s ↦ ?_⟩
    obtain ⟨T, hT, hcov⟩ := hf s
    refine J.superset_covering (fun V g hg ↦ ?_) hT
    obtain ⟨i, t, ht⟩ := hcov g hg
    refine ⟨(Sigma.ι G i).hom.app (op V) t, ?_⟩
    rw [← ht, ← NatTrans.comp_app_apply, ← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_desc]

/-- A family `(q_k : G_k ⟶ F)_{k ∈ K}` of morphisms of
sheaves of sets which induces a surjection out of the coproduct, composed with a family over
each of its sources which does the same, induces a surjection out of the coproduct again. -/
theorem isLocallySurjective_sigmaDesc_comp {F : Sheaf J (Type max u v)}
    {K : Type max u v} {G : K → Sheaf J (Type max u v)} (q : ∀ k, G k ⟶ F)
    {I : K → Type max u v} {H : ∀ k, I k → Sheaf J (Type max u v)} (w : ∀ k i, H k i ⟶ G k)
    (hq : IsLocallySurjective (Sigma.desc q))
    (hw : ∀ k, IsLocallySurjective (Sigma.desc (w k))) :
    IsLocallySurjective (Sigma.desc fun p : Σ k, I k ↦ w p.1 p.2 ≫ q p.1) := by
  rw [isLocallySurjective_iff_epi]
  refine ⟨fun g h hgh ↦ (cancel_epi (Sigma.desc q)).1 (Sigma.hom_ext _ _ fun k ↦ ?_)⟩
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_desc]
  refine (cancel_epi (Sigma.desc (w k))).1 (Sigma.hom_ext _ _ fun i ↦ ?_)
  simpa only [← Category.assoc, Sigma.ι_desc] using
    Sigma.ι (fun p : Σ k, I k ↦ H p.1 p.2) ⟨k, i⟩ ≫= hgh

/-! ### Base change of a surjection along a morphism of sheaves -/

/-- A section `h` of `H`
and a section `t` of `F` over the same object `V` which have the same image in `G` come from a
section of `H ×_G F` over `V`. -/
theorem exists_pullback_section {F G H : Sheaf J (Type max u v)} (ψ : H ⟶ G) (φ : F ⟶ G) {V : C}
    (h : H.obj.obj (op V)) (t : F.obj.obj (op V))
    (heq : ψ.hom.app (op V) h = φ.hom.app (op V) t) :
    ∃ k : (pullback ψ φ).obj.obj (op V),
      (pullback.fst ψ φ).hom.app (op V) k = h ∧ (pullback.snd ψ φ).hom.app (op V) k = t := by
  have hcomm : (sectionEquiv J).symm h ≫ ψ = (sectionEquiv J).symm t ≫ φ := by
    rw [← sectionEquiv_symm_comp, ← sectionEquiv_symm_comp, heq]
  refine ⟨sectionEquiv J (pullback.lift _ _ hcomm), ?_, ?_⟩
  · rw [← sectionEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
  · rw [← sectionEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- If a family `(ψ_i : H_i ⟶ G)_{i ∈ I}` of
morphisms of sheaves of sets induces a surjection, then so does the family of second projections
`(H_i ×_G F ⟶ F)_{i ∈ I}` obtained by pulling it back along any `φ : F ⟶ G`. -/
theorem isLocallySurjective_sigmaDesc_pullback_snd {F G : Sheaf J (Type max u v)} (φ : F ⟶ G)
    {I : Type max u v} {H : I → Sheaf J (Type max u v)} (ψ : ∀ i, H i ⟶ G)
    (hψ : IsLocallySurjective (Sigma.desc ψ)) :
    IsLocallySurjective (Sigma.desc fun i ↦ pullback.snd (ψ i) φ) := by
  refine (isLocallySurjective_sigmaDesc_iff _).2 fun U s ↦ ?_
  obtain ⟨T, hT, hcov⟩ := (isLocallySurjective_sigmaDesc_iff ψ).1 hψ (φ.hom.app (op U) s)
  refine ⟨T, hT, fun V g hg ↦ ?_⟩
  obtain ⟨i, h, heq⟩ := hcov g hg
  rw [← φ.hom.naturality_apply g.op s] at heq
  obtain ⟨k, -, hk⟩ := exists_pullback_section (ψ i) φ h (F.obj.map g.op s) heq
  exact ⟨i, k, hk⟩

/-! ### Quasi-compactness along surjections -/

/-- Quasi-compactness of a sheaf of sets passes along a surjection `φ : F ⟶ G`. -/
@[stacks 0GMP "(2)"]
theorem isQuasiCompact_of_isLocallySurjective {F G : Sheaf J (Type max u v)} (φ : F ⟶ G)
    (hφ : IsLocallySurjective φ) (hF : IsQuasiCompact F) :
    IsQuasiCompact G := by
  intro I H ψ hψ
  obtain ⟨T, hTfin, hT⟩ := hF I (fun i ↦ pullback (ψ i) φ) (fun i ↦ pullback.snd (ψ i) φ)
    (isLocallySurjective_sigmaDesc_pullback_snd φ ψ hψ)
  refine ⟨T, hTfin, isLocallySurjective_of_sigmaDesc_fac
    (f := fun j : T ↦ pullback.snd (ψ j.1) φ ≫ φ) ?_
    (fun j : T ↦ pullback.fst (ψ j.1) φ ≫ Sigma.ι (fun j : T ↦ H j.1) j)
    (fun j ↦ by rw [Category.assoc, Sigma.ι_desc]; exact pullback.condition)⟩
  rw [← sigmaDesc_comp]
  infer_instance

/-- If `f : U ⟶ V` sheafifies to a surjection `h_U^# ⟶ h_V^#` of sheafified representables and
`h_U^#` is quasi-compact, then so is `h_V^#`. -/
@[stacks 0GMP "(1)"]
theorem isQuasiCompact_sheafifiedYoneda_of_isLocallySurjective {U V : C} (f : U ⟶ V)
    (hf : IsLocallySurjective ((sheafifiedYoneda J).map f))
    (hU : IsQuasiCompact ((sheafifiedYoneda J).obj U)) :
    IsQuasiCompact ((sheafifiedYoneda J).obj V) :=
  isQuasiCompact_of_isLocallySurjective _ hf hU

end CategoryTheory.Sheaf
