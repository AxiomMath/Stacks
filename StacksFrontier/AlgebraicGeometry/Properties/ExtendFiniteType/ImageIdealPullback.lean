module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.ImageIdealSupport

/-!
# The vanishing locus of the image of a pulled-back morphism

Let `f : X ⟶ Y` be a morphism of schemes, `A` a quasi-coherent `𝒪_Y`-module and
`φ : A ⟶ 𝒪_Y`.  Pulling back gives a morphism `f^*A ⟶ f^*𝒪_Y ≅ 𝒪_X`, and this file identifies
the vanishing locus of its image with the preimage of the vanishing locus of the image of `φ`:

```
(idealSheafDataOfHom (f^*A) (f^*φ ≫ pullbackUnitIso f)).support
  = f⁻¹ (idealSheafDataOfHom A φ).support
```

Both inclusions are proved from the pointwise criterion
`AlgebraicGeometry.notMem_support_idealSheafDataOfHom_iff`.  One of them needs only that a
section of `A` over `U` pulls back to a section of `f^*A` over `f⁻¹U` whose value is the
restriction of the value of the original (the unit of `f^* ⊣ f_*` on sections).  The other needs
that the sections of `f^*A` over an affine open are *generated* by such pulled-back sections,
which is `AlgebraicGeometry.span_pullbackSection_eq_top` — available for an arbitrary
quasi-coherent `A`, so no finiteness hypothesis on `A` and no hypothesis on `f` is required.

Also recorded is the behaviour of the image ideal sheaf under precomposition with an
epimorphism: the vanishing locus does not change.  That is the step which, in a limit of
schemes, identifies the ideal cut out by a descended morphism out of a finite locally free
module with the one it was built to resolve.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackSectionHom`: the
  identification `f^*𝒪_Y ≅ 𝒪_X` carries the pullback of a function to its image under
  `AlgebraicGeometry.Scheme.Hom.appLE`.
* `AlgebraicGeometry.structureAppₗ_pullbackSectionHom`: the value of the pulled-back morphism on
  a pulled-back section is the pullback of the value.
* `AlgebraicGeometry.coe_support_idealSheafDataOfHom_pullback_of_appLE` and
  `AlgebraicGeometry.coe_support_idealSheafDataOfHom_pullback`: **the vanishing locus of the
  image of a pulled-back morphism**, first for any morphism to the structure sheaf satisfying
  the section-level formula and then for the pullback itself.
* `AlgebraicGeometry.coe_support_idealSheafDataOfHom_of_epi`: precomposition with an
  epimorphism does not change the vanishing locus of the image.
* `AlgebraicGeometry.not_forall_coe_support_idealSheafDataOfHom_comp_eq`: **that statement is
  false without the epimorphism** — a refutation at `ε = 0`, `χ = 𝟙` on `Spec ℤ`, which pins the
  epimorphism as what the proof rests on.

## Implementation notes

The main statement is proved first in a form where the morphism `ψ : f^*A ⟶ 𝒪_X` is a *variable*
constrained by its values on pulled-back sections, and only then specialised to
`f^*φ ≫ pullbackUnitIso f`.  The reason is a transparency obstruction: the target of
`(Scheme.Modules.pullback f).map φ` is `(Scheme.Modules.pullback f).obj (structureModule Y)`
while the source of `(Scheme.Modules.pullbackUnitIso f).hom` is
`(Scheme.Modules.pullback f).obj (Scheme.unitModule Y)`, and
`AlgebraicGeometry.Scheme.unitModule` is a semireducible definition, so the composite is not
type-correct at `implicit` transparency.  A `rewrite` whose motive abstracts a subterm of such a
goal is rejected.  With `ψ` a variable there is nothing to abstract, and the specialisation is an
application, which elaborates at `default` transparency.

The same device is used for `coe_support_idealSheafDataOfHom_of_epi`, whose hypothesis is an
equation `ψ = ε ≫ χ` rather than a composite appearing in the conclusion: at the point of use
`ψ` is the pullback composite above.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 0F8B](https://stacks.math.columbia.edu/tag/0F8B)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

/-- **The identification of the pullback of the structure sheaf with the structure sheaf, on
pulled-back sections.**  For `f : X ⟶ Y` and a function `s` on an open `U` of `Y`, the section
of `f^*𝒪_Y` over `V ≤ f⁻¹U` obtained from `s` by the unit of `f^* ⊣ f_*` is carried by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` to `AlgebraicGeometry.Scheme.Hom.appLE` of
`s`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv` — the statement that the
identification transposes to the ring map of `f` — read on sections over `U` and then restricted
to `V`. -/
theorem Scheme.Modules.pullbackUnitIso_hom_app_pullbackSectionHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    (Scheme.Modules.pullbackUnitIso f).hom.app V
        (pullbackSectionHom f (Scheme.unitModule Y) U V h s)
      = f.appLE U V h s := by
  have h0 : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Scheme.unitModule Y) ≫
      (Scheme.Modules.pushforward f).map (Scheme.Modules.pullbackUnitIso f).hom =
      Scheme.Modules.unitToPushforwardUnit f :=
    Scheme.Modules.pullbackUnitIso_homEquiv f
  have he := congrArg (fun k => k.app U s) h0
  change (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (Scheme.unitModule Y)).app U s) = f.app U s at he
  have hnat := Scheme.Modules.Hom.app_presheaf_map (Scheme.Modules.pullbackUnitIso f).hom
    (homOfLE h : V ⟶ f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Scheme.unitModule Y)).app U s)
  change (Scheme.Modules.pullbackUnitIso f).hom.app V
      (pullbackSectionHom f (Scheme.unitModule Y) U V h s) = _ at hnat
  rw [hnat, he]
  rfl

/-- **The value of a pulled-back morphism on a pulled-back section.**  The pullback of
`φ : A ⟶ 𝒪_Y` sends the pullback of a section `a` of `A` over `U` to the pullback of the value
`φ(a)`, read through `AlgebraicGeometry.Scheme.Hom.appLE`. -/
theorem structureAppₗ_pullbackSectionHom {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules)
    (φ : A ⟶ structureModule Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : Γ(A, U)) :
    structureAppₗ ((Scheme.Modules.pullback f).map φ ≫ (Scheme.Modules.pullbackUnitIso f).hom) V
        (pullbackSectionHom f A U V h a)
      = f.appLE U V h (structureAppₗ φ U a) := by
  have hnat : ((Scheme.Modules.pullback f).map φ).app V (pullbackSectionHom f A U V h a)
      = pullbackSectionHom f (Scheme.unitModule Y) U V h (structureAppₗ φ U a) :=
    Scheme.Modules.pullbackSection_naturality f φ U V h a
  show (Scheme.Modules.pullbackUnitIso f).hom.app V
      (((Scheme.Modules.pullback f).map φ).app V (pullbackSectionHom f A U V h a)) = _
  rw [hnat]
  exact Scheme.Modules.pullbackUnitIso_hom_app_pullbackSectionHom f U V h (structureAppₗ φ U a)

/-- If a value of `ψ` is invertible at `x`, so is the value on the restriction to a smaller open
containing `x`. -/
private theorem mem_basicOpen_structureAppₗ_restrict {X : Scheme.{u}} {A : X.Modules}
    (ψ : A ⟶ structureModule X) {V W : X.Opens} (hVW : V ≤ W) (b : Γ(A, W)) {x : X} (hxV : x ∈ V)
    (hx : x ∈ X.basicOpen (structureAppₗ ψ W b)) :
    x ∈ X.basicOpen (structureAppₗ ψ V (A.presheaf.map (homOfLE hVW).op b)) := by
  rw [← map_structureAppₗ ψ hVW b, Scheme.basicOpen_res]
  exact ⟨hxV, hx⟩

/-- **The vanishing locus of the image of a pulled-back morphism**, for any morphism
`ψ : f^*A ⟶ 𝒪_X` whose value on a pulled-back section is the pullback of the value of `φ`.

One inclusion is the pulled-back section itself: a function on `Y` not vanishing at `f x` has a
pullback not vanishing at `x`.  The other is the generating property
`AlgebraicGeometry.span_pullbackSection_eq_top`: over an affine pair the sections whose value
vanishes at `x` form a submodule, and if every value of `φ` vanishes at `f x` then that
submodule contains every pulled-back section, hence everything. -/
theorem coe_support_idealSheafDataOfHom_pullback_of_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Y.Modules) [A.IsQuasicoherent] (φ : A ⟶ structureModule Y)
    (ψ : (Scheme.Modules.pullback f).obj A ⟶ structureModule X)
    (hψ : ∀ (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : Γ(A, U)),
      structureAppₗ ψ V (pullbackSectionHom f A U V h a)
        = f.appLE U V h (structureAppₗ φ U a)) :
    ((idealSheafDataOfHom ((Scheme.Modules.pullback f).obj A) ψ).support : Set X)
      = f.base ⁻¹' ((idealSheafDataOfHom A φ).support : Set Y) := by
  classical
  apply subset_antisymm
  · intro x hx
    by_contra hfx
    obtain ⟨W, a, hWa⟩ :=
      exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom A φ hfx
    refine (notMem_support_idealSheafDataOfHom_of_mem_basicOpen
      ((Scheme.Modules.pullback f).obj A) ψ
      (pullbackSectionHom f A W (f ⁻¹ᵁ W) le_rfl a) ?_) hx
    rw [hψ W (f ⁻¹ᵁ W) le_rfl a, Scheme.basicOpen_appLE]
    exact ⟨Y.basicOpen_le _ hWa, hWa⟩
  · intro x hx
    by_contra hnx
    obtain ⟨W, b, hWb⟩ :=
      exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom
        ((Scheme.Modules.pullback f).obj A) ψ hnx
    obtain ⟨-, ⟨U, hUaff, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (show f.base x ∈ ((⊤ : Y.Opens) : Set Y) from trivial) (⊤ : Y.Opens).isOpen
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((X.basicOpen (structureAppₗ ψ W b) ⊓ f ⁻¹ᵁ U : X.Opens) : Set X)
          from ⟨hWb, hxU⟩)
        (X.basicOpen (structureAppₗ ψ W b) ⊓ f ⁻¹ᵁ U).isOpen
    have hVle' : V ≤ X.basicOpen (structureAppₗ ψ W b) ⊓ f ⁻¹ᵁ U := hVle
    have hVW : V ≤ W := le_trans (le_trans hVle' inf_le_left) (X.basicOpen_le _)
    have hVU : V ≤ f ⁻¹ᵁ U := le_trans hVle' inf_le_right
    have hP : ∀ t : Γ((Scheme.Modules.pullback f).obj A, V),
        x ∉ X.basicOpen (structureAppₗ ψ V t) := by
      have htop : (⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pullback f).obj A, V)) ≤
          { carrier := {t | x ∉ X.basicOpen (structureAppₗ ψ V t)}
            zero_mem' := by simp
            add_mem' := by
              intro t u ht hu hmem
              rw [map_add] at hmem
              exact (X.basicOpen_add_le _ _ hmem).elim ht hu
            smul_mem' := by
              intro c t ht hmem
              rw [LinearMap.map_smul, smul_eq_mul, Scheme.basicOpen_mul] at hmem
              exact ht hmem.2 } := by
        rw [← span_pullbackSection_eq_top f A hUaff hVaff hVU]
        refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun a hmem => ?_)
        rw [hψ U V hVU a, Scheme.basicOpen_appLE] at hmem
        exact notMem_support_idealSheafDataOfHom_of_mem_basicOpen A φ a hmem.2 hx
      exact fun t => htop (show t ∈ (⊤ : Submodule Γ(X, V)
        Γ((Scheme.Modules.pullback f).obj A, V)) from Submodule.mem_top)
    exact hP _ (mem_basicOpen_structureAppₗ_restrict ψ hVW b hxV hWb)

/-- **The vanishing locus of the image of a pulled-back morphism.**  For a quasi-coherent
`𝒪_Y`-module `A` and `φ : A ⟶ 𝒪_Y`, the vanishing locus of the image of the pullback of `φ` is
the preimage of the vanishing locus of the image of `φ`.

No finiteness hypothesis on `A` and no hypothesis on `f` are needed. -/
theorem coe_support_idealSheafDataOfHom_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Y.Modules) [A.IsQuasicoherent] (φ : A ⟶ structureModule Y) :
    ((idealSheafDataOfHom ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).map φ ≫
          (Scheme.Modules.pullbackUnitIso f).hom)).support : Set X)
      = f.base ⁻¹' ((idealSheafDataOfHom A φ).support : Set Y) :=
  coe_support_idealSheafDataOfHom_pullback_of_appLE f A φ _ (structureAppₗ_pullbackSectionHom f A φ)

/-- **Precomposition with an epimorphism does not change the vanishing locus of the image.**
If `ψ = ε ≫ χ` with `ε` an epimorphism of quasi-coherent modules, then `ψ` and `χ` have the same
image vanishing locus.

One inclusion holds because the image of `ψ` is contained in that of `χ`.  The other is the
section-level form of surjectivity of an epimorphism
(`Stacks.SheafOfModules.StalkEpiMono.exists_sections_of_epi`): a section of the target is, near
each of its points, the image of a section of the source, and the values then agree there. -/
theorem coe_support_idealSheafDataOfHom_of_epi {X : Scheme.{u}} {A B : X.Modules}
    [A.IsQuasicoherent] [B.IsQuasicoherent] (ε : A ⟶ B) [hε : Epi ε]
    (χ : B ⟶ structureModule X) (ψ : A ⟶ structureModule X) (hψ : ψ = ε ≫ χ) :
    ((idealSheafDataOfHom A ψ).support : Set X)
      = ((idealSheafDataOfHom B χ).support : Set X) := by
  have hepi : @Epi (SheafOfModules X.ringCatSheaf) _ _ _ ε :=
    ⟨fun g₁ g₂ h => hε.left_cancellation g₁ g₂ h⟩
  have happ : ∀ (V : X.Opens) (t : Γ(A, V)),
      structureAppₗ ψ V t = structureAppₗ χ V (ε.app V t) := by
    intro V t; rw [hψ]; rfl
  apply subset_antisymm
  · intro x hx
    by_contra hnx
    obtain ⟨W, b, hWb⟩ := exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom B χ hnx
    have hxW : x ∈ W := X.basicOpen_le _ hWb
    obtain ⟨V, hVW, hxV, s, hs⟩ :=
      Stacks.SheafOfModules.StalkEpiMono.exists_sections_of_epi ε W b x hxW
    refine notMem_support_idealSheafDataOfHom_of_mem_basicOpen A ψ s ?_ hx
    have hsb : ε.app V s = B.presheaf.map (homOfLE hVW).op b := hs
    rw [happ V s, hsb]
    exact mem_basicOpen_structureAppₗ_restrict χ hVW b hxV hWb
  · intro x hx
    by_contra hnx
    obtain ⟨W, a, hWa⟩ := exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom A ψ hnx
    refine notMem_support_idealSheafDataOfHom_of_mem_basicOpen B χ (ε.app W a) ?_ hx
    rw [← happ W a]
    exact hWa

/-! ### The epimorphism in `coe_support_idealSheafDataOfHom_of_epi` is load-bearing -/

/-- The image of the zero morphism is the zero sheaf of ideals, whose vanishing locus is the
whole scheme: no value of the zero morphism is invertible anywhere. -/
theorem mem_support_idealSheafDataOfHom_zero (X : Scheme.{u}) (x : X) :
    x ∈ ((idealSheafDataOfHom (structureModule X)
      (0 : structureModule X ⟶ structureModule X)).support : Set X) := by
  by_contra hx
  obtain ⟨W, a, hWa⟩ :=
    exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom (structureModule X) 0 hx
  rw [show structureAppₗ (0 : structureModule X ⟶ structureModule X) W a = 0 from rfl,
    Scheme.basicOpen_zero] at hWa
  exact hWa

/-- The image of the identity of the structure sheaf is the unit sheaf of ideals, whose vanishing
locus is empty: the value at the global section `1` is invertible everywhere. -/
theorem notMem_support_idealSheafDataOfHom_id (X : Scheme.{u}) (x : X) :
    x ∉ ((idealSheafDataOfHom (structureModule X) (𝟙 (structureModule X))).support : Set X) := by
  refine notMem_support_idealSheafDataOfHom_of_mem_basicOpen (structureModule X) (𝟙 _)
    (W := ⊤) (1 : Γ(X, ⊤)) ?_
  rw [show structureAppₗ (𝟙 (structureModule X)) ⊤ (1 : Γ(X, ⊤)) = 1 from rfl,
    Scheme.basicOpen_one]
  trivial

/-- **`coe_support_idealSheafDataOfHom_of_epi` is false without the epimorphism.**  Dropping
`Epi ε` from that statement leaves a well-typed assertion which is refuted by `ε = 0`,
`χ = 𝟙` on `Spec ℤ`: the image of `0 ≫ 𝟙 = 0` is the zero sheaf of ideals, whose vanishing locus
is all of `Spec ℤ`, while the image of `𝟙` is the unit sheaf of ideals, whose vanishing locus is
empty.

So the epimorphism is exactly what makes the two images agree, which is where
`Stacks.SheafOfModules.StalkEpiMono.exists_sections_of_epi` is spent in the proof. -/
theorem not_forall_coe_support_idealSheafDataOfHom_comp_eq :
    ¬ ∀ (X : Scheme.{u}) (ε χ ψ : structureModule X ⟶ structureModule X), ψ = ε ≫ χ →
        ((idealSheafDataOfHom (structureModule X) ψ).support : Set X)
          = ((idealSheafDataOfHom (structureModule X) χ).support : Set X) := by
  intro H
  obtain ⟨x⟩ : Nonempty ↥(Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (CommRingCat.of (ULift.{u} ℤ))))
  have h := H (Spec (CommRingCat.of (ULift.{u} ℤ))) 0 (𝟙 _) 0 (by simp)
  exact notMem_support_idealSheafDataOfHom_id _ x
    (h ▸ mem_support_idealSheafDataOfHom_zero _ x)

end AlgebraicGeometry

end
