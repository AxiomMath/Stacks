module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion

/-!
# The comparison map on direct images of forms: composition, sections, transport

For a morphism `f : Y ⟶ X` of schemes over `π : X ⟶ S`,
`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison f π d` is the canonical map
`Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}` (the transpose under `f^* ⊣ f_*` of the canonical map of
[Stacks, Tag 01UV]). This file proves the general facts about it that the source's proof of
clause (2) of [Stacks, Tag 0FUR] uses without comment:

* it is compatible with composition: the map of `g ≫ f` is the map of `f` followed by `f_*` of
  the map of `g`;
* consequently, if `f` has a section, the map of `f` is a split monomorphism, the map of the
  identity being an isomorphism;
* it transports along isomorphisms of schemes over the target.

It also records two facts about quasi-coherent modules on an affine scheme `X`: one with no global
sections is zero, and a split monomorphism `M ⟶ N` is an isomorphism as soon as `N ≅ M` abstractly
and `Γ(X, M)` is a finite `Γ(X, 𝒪_X)`-module. The second holds because a surjective endomorphism of
a finite module over a commutative ring is injective (Vasconcelos; Mathlib's
`OrzechProperty.injective_of_surjective_endomorphism`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison_comp`: the composition law.
* `AlgebraicGeometry.Scheme.Hom.isSplitMono_formsDirectImageComparison_of_section`: the map of a
  morphism with a section is a split monomorphism.
* `AlgebraicGeometry.Scheme.Hom.pushforwardFormsIsoOfIso` and
  `AlgebraicGeometry.Scheme.Hom.subsingleton_sections_relativeDifferentialForms_of_iso`: transport
  along an isomorphism over the target.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isSplitMono_of_iso`: the affine
  split-monomorphism criterion.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y W S : Scheme.{u}}

/-- **The comparison map on direct images of forms is compatible with composition.** For
`g : W ⟶ Y` and `f : Y ⟶ X` over `π : X ⟶ S`, the map `Ω^d_{X/S} ⟶ (g ≫ f)_*Ω^d_{W/S}` is the map
of `f` followed by `f_*` of the map of `g`, read through `f_* ∘ g_* = (g ≫ f)_*`. -/
theorem formsDirectImageComparison_comp (f : Y ⟶ X) (g : W ⟶ Y) (π : X ⟶ S) (d : ℤ) :
    formsDirectImageComparison (g ≫ f) π d =
      formsDirectImageComparison f π d ≫
        (Scheme.Modules.pushforward f).map (formsDirectImageComparison g (f ≫ π) d) ≫
        (Scheme.Modules.pushforwardComp g f).hom.app _ := by
  have hφ := relativeDifferentialFormsMap_comp f g π (f ≫ π) ((g ≫ f) ≫ π) (𝟙 S) (𝟙 S) (𝟙 S)
    (by simp) (by simp) (by simp) d
  have hu := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)) (Scheme.Modules.pullbackComp g f).inv
    (relativeDifferentialForms π d)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at hu
  simp only [formsDirectImageComparison]
  rw [hφ, Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hu]
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
    (relativeDifferentialFormsMap f π (f ≫ π) (𝟙 S) (by simp) d)
  simp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← (Scheme.Modules.pushforwardComp g f).hom.naturality_assoc,
    ← (Scheme.Modules.pushforwardComp g f).hom.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [Functor.map_comp, reassoc_of% hn]
  rfl

/-- **If `f` has a section, the comparison map of `f` is a split monomorphism.** By the
composition law, the map of `σ ≫ f = 𝟙` factors through the map of `f`, and the map of an
isomorphism is an isomorphism. -/
theorem isSplitMono_formsDirectImageComparison_of_section (f : Y ⟶ X) (σ : X ⟶ Y)
    (hσ : σ ≫ f = 𝟙 X) (π : X ⟶ S) (d : ℤ) :
    IsSplitMono (formsDirectImageComparison f π d) := by
  have : IsIso (σ ≫ f) := hσ ▸ inferInstance
  have h := isIso_formsDirectImageComparison_of_isIso (σ ≫ f) π d
  rw [formsDirectImageComparison_comp] at h
  obtain ⟨g, hg, -⟩ := h.out
  exact IsSplitMono.mk' ⟨((Scheme.Modules.pushforward f).map
      (formsDirectImageComparison σ (f ≫ π) d) ≫
        (Scheme.Modules.pushforwardComp σ f).hom.app _) ≫ g,
    (Category.assoc _ _ _).symm.trans hg⟩

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-- **On an affine scheme a split monomorphism of quasi-coherent modules `c : M ⟶ N` with
`N ≅ M` and `Γ(X, M)` finite is an isomorphism.** On global sections, the retraction of `c`
composed with the inverse of `N ≅ M` is a surjective endomorphism of a finite module, hence
injective. So the retraction is injective, `c` is bijective on global sections, and
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top` applies. -/
theorem isIso_of_isSplitMono_of_iso {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (c : M ⟶ N) [IsSplitMono c] (e : N ≅ M)
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)] : IsIso c := by
  refine isIso_of_isIso_app_top c ?_
  set r := retraction c
  have key {A B : X.Modules} (a : A ⟶ B) (b : B ⟶ A) (h : a ≫ b = 𝟙 A) (x) :
      b.app ⊤ (a.app ⊤ x) = x := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, h]
    rfl
  have hcr := key c r (IsSplitMono.id c)
  have hie := key e.hom e.inv e.hom_inv_id
  let ψ : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(M, ⊤) :=
    { toFun := fun x => r.app ⊤ (e.inv.app ⊤ x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp }
  have hψs : Function.Surjective ψ := fun x =>
    ⟨e.hom.app ⊤ (c.app ⊤ x), by simp [ψ, hie, hcr]⟩
  have hri : Function.Injective fun w => r.app ⊤ w := fun w₁ w₂ hw =>
    (hie w₁).symm.trans <| (congrArg (e.inv.app ⊤)
      (OrzechProperty.injective_of_surjective_endomorphism ψ hψs
        (a₁ := e.hom.app ⊤ w₁) (a₂ := e.hom.app ⊤ w₂) (by simpa [ψ, hie] using hw))).trans (hie w₂)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨Function.LeftInverse.injective hcr, fun y => ⟨r.app ⊤ y, hri (hcr _)⟩⟩

end Stacks.AlgebraicGeometry.AffineBaseChange

namespace AlgebraicGeometry.Scheme.Hom

/-- **Direct images of forms transport along an isomorphism of schemes over the target.** If
`e : W ≅ P` carries `f : W ⟶ Z` to `q : P ⟶ Z`, then `q_*Ω^d_{P/S} ≅ f_*Ω^d_{W/S}`: the
comparison map of `e` is an isomorphism, followed by `q_* ∘ e_* = f_*`. -/
def pushforwardFormsIsoOfIso {W P Z S : Scheme.{u}} (e : W ≅ P) {q : P ⟶ Z} {f : W ⟶ Z}
    (h : e.hom ≫ q = f) (π : Z ⟶ S) (d : ℤ) :
    (Scheme.Modules.pushforward q).obj (relativeDifferentialForms (q ≫ π) d) ≅
      (Scheme.Modules.pushforward f).obj (relativeDifferentialForms (f ≫ π) d) := by
  subst h
  haveI := isIso_formsDirectImageComparison_of_isIso e.hom (q ≫ π) d
  exact (Scheme.Modules.pushforward q).mapIso
      (asIso (formsDirectImageComparison e.hom (q ≫ π) d)) ≪≫
    (Scheme.Modules.pushforwardComp e.hom q).app _

/-- **Vanishing of global forms transports along an isomorphism of schemes over the base**: if
`e : W ≅ P` carries `f` to `q` and `Ω^d_{P/B}` has no nonzero global sections, neither does
`Ω^d_{W/B}`. -/
theorem subsingleton_sections_relativeDifferentialForms_of_iso {W P B : Scheme.{u}} (e : W ≅ P)
    {q : P ⟶ B} {f : W ⟶ B} (h : e.hom ≫ q = f) (d : ℤ)
    (hP : Subsingleton Γ(relativeDifferentialForms q d, ⊤)) :
    Subsingleton Γ(relativeDifferentialForms f d, ⊤) := by
  subst h
  have := isIso_formsDirectImageComparison_of_isIso e.hom q d
  exact ((ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso ((formsDirectImageComparison e.hom q d).app ⊤))).2.subsingleton

end AlgebraicGeometry.Scheme.Hom
