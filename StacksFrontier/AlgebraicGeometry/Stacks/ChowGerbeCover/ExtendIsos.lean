module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.SectionFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenSubspaceOfRepr
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints


/-!
# Extending the isomorphisms of the proof of Stacks 0CQ7 by admissible blowups

In the proof of [Stacks, Tag 0CQ7], step `(f) → (g)`, there are local sections `xᵢ : Uᵢ ⟶ 𝒳` of
a separated `f : 𝒳 ⟶ Y` over quasi-compact opens `Uᵢ` of a quasi-compact quasi-separated space,
and isomorphisms `ψᵢⱼ : xᵢ ≅ xⱼ` over a quasi-compact open `V ⊆ ⋂ Uᵢ` satisfying the cocycle
condition. The morphisms `Isom(xᵢ, xⱼ) ⟶ Uᵢ ∩ Uⱼ` are proper because `f` is separated, `ψᵢⱼ` is
a section of it over `V`, and Stacks 0CPI extends that section to all of `Uᵢ ∩ Uⱼ` after a
`V`-admissible blowup. This file carries out that step, one pair `(i, j)` at a time: each blowup
is taken over the previous one, and the isomorphisms already extended are restricted along it.

Stacks 0CPI and the properness of the isomorphism spaces enter as the hypotheses `h0CPI` and
`hproper`.

## Main definitions

* `AlgebraicGeometry.Stack.IsomFamily.toSectionOver` and
  `AlgebraicGeometry.Stack.IsomFamily.ofSectionOver`: the dictionary between families of
  isomorphisms over `Z'` of two points pulled back along `g : Z' ⟶ Z` and sections of their
  isomorphism space over `g`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.HasIsoExtension`: an extension along
  `r : Y₁ ⟶ Y₀` of a family of isomorphisms over `V₀` to `r⁻¹(Uᵢ ∩ Uⱼ)`.

## Main results

* `AlgebraicGeometry.Stack.IsomFamily.exists_isAdmissibleBlowup_extension`: Stacks 0CPI read for
  families of isomorphisms.
* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.exists_isos_of_isosOn`: the step
  `(f) → (g)` of the proof of Stacks 0CQ7.
* `AlgebraicGeometry.Space.IsAdmissibleBlowup.range_subset_image_range_preimage`: every point of
  `U` lifts along a `U`-admissible blowup.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CPI](https://stacks.math.columbia.edu/tag/0CPI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The intersection of two quasi-compact open subspaces of a quasi-separated algebraic space is
quasi-compact.** Its points are the intersection of the two compact open point sets, compact
because the point space is quasi-separated. -/
theorem isQuasiCompactSpace_inf_of_isAbsolutelyQuasiSeparated
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X) {G₁ G₂ : Subfunctor X}
    (hG₁ : IsOpenSubspace B S hS G₁) (hG₂ : IsOpenSubspace B S hS G₂)
    (h₁ : IsQuasiCompactSpace B S hS G₁.toFunctor) (h₂ : IsQuasiCompactSpace B S hS G₂.toFunctor) :
    IsQuasiCompactSpace B S hS (G₁ ⊓ G₂).toFunctor := by
  have := quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  have hopen : ∀ {G : Subfunctor X} (hG : IsOpenSubspace B S hS G),
      IsOpen (Set.range (pointsMap B S hS G.toFunctor G.ι)) := fun {G} hG => by
    rw [← openSubspacesOrderIso_apply B S hS X hX ⟨G, hG⟩]
    exact (openSubspacesOrderIso B S hS X hX ⟨G, hG⟩).2
  refine isQuasiCompactSpace_of_isCompact_range B S hS hX
    (isOpenSubspace_inf B S hS hX _ _ hG₁ hG₂) ?_
  have e := subspacePointSet_inf B S hS G₁ G₂
  simp only [subspacePointSet] at e
  rw [e]
  exact QuasiSeparatedSpace.inter_isCompact _ _ (hopen hG₁)
    (isCompact_range_of_isQuasiCompactSpace B S hS hG₁ h₁) (hopen hG₂)
    (isCompact_range_of_isQuasiCompactSpace B S hS hG₂ h₂)

/-- **An algebraic space proper over a quasi-compact quasi-separated one is quasi-compact and
quasi-separated**: a proper morphism is quasi-compact and separated, hence quasi-separated
(Stacks 03KK), and Stacks 04ZH, part (2) applies. -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    IsQuasiCompactSpace B S hS X ∧ IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X :=
  ⟨isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc f hf.2.1.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hX hYqs
      (isQuasiSeparated_of_isSeparated B S hS hf.1)⟩

variable {B S hS}

/-- **Every point of `U` lifts along a `U`-admissible blowup to a point of the inverse image of
`U`.** The centre is disjoint from `U`, so `U` lies in the open complement of the centre, over
which the blowup is an isomorphism (Stacks 085T, part (1)). -/
theorem IsAdmissibleBlowup.range_subset_image_range_preimage {X X' : AlgebraicSpaces B S hS}
    {U : OpenSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsAdmissibleBlowup B S hS U b) :
    Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) ⊆
      pointsMap B S hS X'.1 b.hom ''
        Set.range (pointsMap B S hS (U.1.preimage b.hom).toFunctor (U.1.preimage b.hom).ι) := by
  obtain ⟨Z, -, hdisj, hbl⟩ := hb
  set C := openComplementOfClosedSubspace B S hS X Z with hC
  have hUC : U ≤ C := by
    rw [← (openSubspacesOrderIso B S hS X.1 X.2).le_iff_le]
    intro x hx
    change x ∈ (openSubspacesOrderIso B S hS X.1 X.2 C).1
    rw [openSubspacesOrderIso_apply]
    change x ∈ subspacePointSet B S hS X.1 C.1
    rw [hC, subspacePointSet_openComplement]
    exact hdisj.subset_compl_right hx
  have := isIso_fromPreimage_openComplement hbl
  intro x hx
  obtain ⟨y, hy⟩ := range_pointsMap_ι_le B S hS (show U.1 ≤ C.1 from hUC) hx
  obtain ⟨y', rfl⟩ := surjective_pointsMap_of_isIso B S hS (asIso (C.1.fromPreimage b.hom)) y
  have hxy : pointsMap B S hS X'.1 b.hom
      (pointsMap B S hS _ (C.1.preimage b.hom).ι y') = x := by
    rw [← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι, pointsMap_comp_apply]
    exact hy
  refine ⟨_, ?_, hxy⟩
  rw [range_pointsMap_preimage_ι, Set.mem_preimage, hxy]
  exact hx

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

namespace IsomFamily

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hZ : IsAlgebraicSpace B S hS Z}
  {hZ' : IsAlgebraicSpace B S hS Z'} {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The section of `Isom_𝒳(x₁, x₂)` over `g : Z' ⟶ Z` named by a natural family of isomorphisms
between the pullbacks of `x₁` and `x₂` to `Z'`. -/
noncomputable def toSectionOver (g : Z' ⟶ Z) {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z' hZ' (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ g ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ g ≫ x₂)) :
    Z' ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂ where
  app T := ↾fun z => ⟨g.app T z, ⟨φ.1 T z, isIso_fiberHom B S hS 𝒳 _⟩⟩
  naturality T₁ T₂ h := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    have hg : g.app T₂ (Z'.map h z) = Z.map h (g.app T₁ z) :=
      ConcreteCategory.congr_hom (g.naturality h) z
    change (⟨g.app T₂ (Z'.map h z), ⟨φ.1 T₂ (Z'.map h z), _⟩⟩ :
        isomSection B S hS Z hZ x₁ x₂ T₂) =
      ⟨Z.map h (g.app T₁ z), ⟨pointRestrict B S hS Z hZ x₁ x₂ h (g.app T₁ z)
        (Z.map h (g.app T₁ z)) rfl (φ.1 T₁ z), _⟩⟩
    refine isomSection_eq_of_pointHomCongr B S hS Z hZ x₁ x₂ _ _ _ rfl hg.symm ?_
    exact (pointHomCongr_eq B S hS Z hZ x₁ x₂ rfl _).trans ((φ.2 h z).symm.trans
      (pointHomCongr_pointRestrict B S hS Z hZ x₁ x₂ h (g.app T₁ z) rfl hg hg.symm _).symm)

/-- `AlgebraicGeometry.Stack.IsomFamily.toSectionOver` is a section over `g`. -/
theorem toSectionOver_proj (g : Z' ⟶ Z) {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z' hZ' (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ g ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ g ≫ x₂)) :
    toSectionOver g φ ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = g := by
  ext T z
  rfl

/-- A section of `Isom_𝒳(x₁, x₂)` over `g` names, over each point `z` of `Z'`, the point `g(z)`. -/
theorem sectionOver_app_fst {g : Z' ⟶ Z} {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    {s : Z' ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂}
    (hs : s ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = g)
    (T : (BigFppfOver B S hS)ᵒᵖ) (z : Z'.obj T) : (s.app T z).1 = g.app T z :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app hs T) z :)

/-- The natural family of isomorphisms between the pullbacks of `x₁` and `x₂` to `Z'` named by a
section of `Isom_𝒳(x₁, x₂)` over `g : Z' ⟶ Z`. -/
noncomputable def ofSectionOver {g : Z' ⟶ Z} {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (s : Z' ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂)
    (hs : s ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = g) :
    IsomFamily B S hS Z' hZ' (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ g ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ g ≫ x₂) :=
  ⟨fun T z => pointHomCongr B S hS Z hZ x₁ x₂ (sectionOver_app_fst hs T z) (s.app T z).2.1,
    fun {T₁ T₂} h z => by
      have hg : g.app T₂ (Z'.map h z) = Z.map h (g.app T₁ z) :=
        ConcreteCategory.congr_hom (g.naturality h) z
      have hnat : s.app T₂ (Z'.map h z) =
          (isomSpaceOverSpace B S hS Z hZ x₁ x₂).map h (s.app T₁ z) :=
        ConcreteCategory.congr_hom (s.naturality h) z
      exact pointRestrict_pointHomCongr_section B S hS Z hZ x₁ x₂ h (s.app T₁ z)
        (s.app T₂ (Z'.map h z)) hnat (g.app T₁ z) (g.app T₂ (Z'.map h z))
        (sectionOver_app_fst hs T₁ z) (sectionOver_app_fst hs T₂ (Z'.map h z)) hg⟩

/-- The value of `AlgebraicGeometry.Stack.IsomFamily.ofSectionOver` at a point is the
isomorphism named by the section there. -/
theorem ofSectionOver_apply {g : Z' ⟶ Z} {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (s : Z' ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂)
    (hs : s ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = g) {T : (BigFppfOver B S hS)ᵒᵖ}
    (z : Z'.obj T) (t : isomSection B S hS Z hZ x₁ x₂ T) (ht : s.app T z = t)
    (h : t.1 = g.app T z) :
    (ofSectionOver (hZ' := hZ') s hs).1 T z = pointHomCongr B S hS Z hZ x₁ x₂ h t.2.1 := by
  subst ht
  rfl

/-- **Stacks 0CPI for natural families of isomorphisms.** Let `x₁, x₂ : W ⟶ 𝒳` be two points over
a quasi-compact open `W` of a quasi-compact quasi-separated algebraic space `Y₁` whose
isomorphism space `Isom(x₁, x₂) ⟶ W` is proper, and `ψ` a family of isomorphisms between their
restrictions to a quasi-compact open `U ⊆ W`. After a `U`-admissible blowup `b`, `ψ` extends to a
family of isomorphisms between the pullbacks of `x₁` and `x₂` to `b⁻¹(W)`: the section of
`Isom(x₁, x₂)` named by `ψ` over `U` extends (`h0CPI`, Stacks 0CPI). -/
theorem exists_isAdmissibleBlowup_extension
    (h0CPI : ∀ {X Y : AlgebraicSpaces B S hS}
      (_hYqc : Space.IsQuasiCompactSpace B S hS Y.1)
      (_hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
      (U W : Space.OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1)
      (_hUqc : Space.IsQuasiCompactSpace B S hS U.1.toFunctor)
      (_hWqc : Space.IsQuasiCompactSpace B S hS W.1.toFunctor)
      (f : X ⟶ Space.openSubspace B S hS Y W) (_hf : Space.IsProper B S hS f.hom)
      (s : U.1.toFunctor ⟶ X.1) (_hs : s ≫ f.hom = Subfunctor.homOfLe hUW),
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), Space.IsAdmissibleBlowup B S hS U b ∧
        ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1, s' ≫ f.hom = W.1.fromPreimage b.hom ∧
          Subfunctor.homOfLe (fun T _ hx => hUW T hx :
            U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' = U.1.fromPreimage b.hom ≫ s)
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₁qc : Space.IsQuasiCompactSpace B S hS Y₁)
    (hY₁qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁)
    (Uo Wo : Space.OpenSubspaces B S hS Y₁) (hUW : Uo.1 ≤ Wo.1)
    (hUqc : Space.IsQuasiCompactSpace B S hS Uo.1.toFunctor)
    (hWqc : Space.IsQuasiCompactSpace B S hS Wo.1.toFunctor)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Wo.1.toFunctor Wo.2.1 ⟶ 𝒳)
    (hprop : Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Wo.1.toFunctor Wo.2.1 x₁ x₂))
    (ψ : IsomFamily B S hS Uo.1.toFunctor Uo.2.1
      (algebraicSpaceStackMap.{u, w} B S hS Uo.2.1 Wo.2.1 (Subfunctor.homOfLe hUW) ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS Uo.2.1 Wo.2.1 (Subfunctor.homOfLe hUW) ≫ x₂)) :
    ∃ (Y₂ : AlgebraicSpaces B S hS) (b : Y₂ ⟶ ⟨Y₁, hY₁⟩), Space.IsAdmissibleBlowup B S hS Uo b ∧
      ∃ φ : IsomFamily B S hS (Wo.1.preimage b.hom).toFunctor
          (Space.isOpenSubspace_preimage B S hS b.hom Wo.1 hY₁ Y₂.2 Wo.2).1
          (algebraicSpaceStackMap.{u, w} B S hS
            (Space.isOpenSubspace_preimage B S hS b.hom Wo.1 hY₁ Y₂.2 Wo.2).1 Wo.2.1
            (Wo.1.fromPreimage b.hom) ≫ x₁)
          (algebraicSpaceStackMap.{u, w} B S hS
            (Space.isOpenSubspace_preimage B S hS b.hom Wo.1 hY₁ Y₂.2 Wo.2).1 Wo.2.1
            (Wo.1.fromPreimage b.hom) ≫ x₂),
        ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (v : Y₂.1.obj T) (hv : v ∈ (Uo.1.preimage b.hom).obj T),
          φ.1 T ⟨v, hUW T hv⟩ = ψ.1 T ⟨b.hom.app T v, hv⟩ := by
  obtain ⟨Y₂, b, hb, s', hs', hres⟩ := h0CPI (Y := ⟨Y₁, hY₁⟩)
    (X := ⟨isomSpaceOverSpace B S hS Wo.1.toFunctor Wo.2.1 x₁ x₂,
      isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS _ Wo.2.1 x₁ x₂⟩)
    hY₁qc hY₁qs Uo Wo hUW hUqc hWqc
    (ObjectProperty.homMk (isomSpaceOverSpaceProj B S hS Wo.1.toFunctor Wo.2.1 x₁ x₂)) hprop
    (toSectionOver (Subfunctor.homOfLe hUW) ψ) (toSectionOver_proj _ ψ)
  refine ⟨Y₂, b, hb, ofSectionOver s' hs', fun T v hv => ?_⟩
  have ht : s'.app T ⟨v, hUW T hv⟩ =
      (toSectionOver (Subfunctor.homOfLe hUW) ψ).app T ⟨b.hom.app T v, hv⟩ :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app hres T) ⟨v, hv⟩ :)
  exact ofSectionOver_apply s' hs' _ _ ht rfl

end IsomFamily

namespace AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W : Subfunctor Y} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀}
  {q₀ : Y₀ ⟶ Y} {ι : Type}

namespace SectionFamily

/-- **An extension of a family of isomorphisms over `V₀` along `r : Y₁ ⟶ Y₀`.** For a pair
`(i, j)` and a family `ψ` of isomorphisms between `x i` and `x j` over `V₀ ⊆ U i ∩ U j`: a family
of isomorphisms between the pullbacks of `x i` and `x j` to `r⁻¹(U i ∩ U j)` which, at every point
of `r⁻¹(V₀)`, is the value of `ψ` at its image. -/
def HasIsoExtension (F : SectionFamily hY f W hY₀ q₀ ι) {V₀ : Subfunctor Y₀}
    (hV₀ : Space.IsOpenSubspace B S hS V₀) (hVU : ∀ i, V₀ ≤ F.U i) {i j : ι}
    (ψ : IsomFamily B S hS V₀.toFunctor hV₀.1
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen i).1 (Subfunctor.homOfLe (hVU i)) ≫
        F.x i)
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen j).1 (Subfunctor.homOfLe (hVU j)) ≫
        F.x j))
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀) :
    Prop :=
  ∃ φ : IsomFamily B S hS ((F.U i ⊓ F.U j).preimage r).toFunctor
      (Space.isOpenSubspace_preimage B S hS r _ hY₀ hY₁ (F.isOpen_inf i j)).1
      (algebraicSpaceStackMap.{u, w} B S hS
        (Space.isOpenSubspace_preimage B S hS r _ hY₀ hY₁ (F.isOpen_inf i j)).1
        (F.isOpen_inf i j).1 ((F.U i ⊓ F.U j).fromPreimage r) ≫ F.left i j)
      (algebraicSpaceStackMap.{u, w} B S hS
        (Space.isOpenSubspace_preimage B S hS r _ hY₀ hY₁ (F.isOpen_inf i j)).1
        (F.isOpen_inf i j).1 ((F.U i ⊓ F.U j).fromPreimage r) ≫ F.right i j),
    ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (v : Y₁.obj T) (hv : v ∈ (V₀.preimage r).obj T),
      φ.1 T ⟨v, hVU i T hv, hVU j T hv⟩ = ψ.1 T ⟨r.app T v, hv⟩

/-- **Extensions restrict.** An extension along `r` gives one along `b ≫ r`, by restricting the
family along `b`. -/
theorem HasIsoExtension.comp {F : SectionFamily hY f W hY₀ q₀ ι} {V₀ : Subfunctor Y₀}
    {hV₀ : Space.IsOpenSubspace B S hS V₀} {hVU : ∀ i, V₀ ≤ F.U i} {i j : ι}
    {ψ : IsomFamily B S hS V₀.toFunctor hV₀.1
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen i).1 (Subfunctor.homOfLe (hVU i)) ≫
        F.x i)
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen j).1 (Subfunctor.homOfLe (hVU j)) ≫
        F.x j)}
    {Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₁ : IsAlgebraicSpace B S hS Y₁} {r : Y₁ ⟶ Y₀}
    (h : F.HasIsoExtension hV₀ hVU ψ hY₁ r) (hY₂ : IsAlgebraicSpace B S hS Y₂) (b : Y₂ ⟶ Y₁) :
    F.HasIsoExtension hV₀ hVU ψ hY₂ (b ≫ r) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨IsomFamily.restrict (Z' := ((F.U i ⊓ F.U j).preimage (b ≫ r)).toFunctor)
    (Space.isOpenSubspace_preimage B S hS (b ≫ r) _ hY₀ hY₂ (F.isOpen_inf i j)).1
    (((F.U i ⊓ F.U j).preimage r).fromPreimage b) φ, fun T v hv => hφ T (b.app T v) hv⟩

/-- The family `ψ` over `V₀`, restricted to `r⁻¹(V₀)` and read as a family between the
restrictions of the pullbacks of `x i` and `x j` to `r⁻¹(U i ∩ U j)`. -/
noncomputable def isosPreimage (F : SectionFamily hY f W hY₀ q₀ ι) {V₀ : Subfunctor Y₀}
    (hV₀ : Space.IsOpenSubspace B S hS V₀) (hVU : ∀ i, V₀ ≤ F.U i) {i j : ι}
    (ψ : IsomFamily B S hS V₀.toFunctor hV₀.1
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen i).1 (Subfunctor.homOfLe (hVU i)) ≫
        F.x i)
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen j).1 (Subfunctor.homOfLe (hVU j)) ≫
        F.x j))
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : Y₁ ⟶ Y₀)
    (hU : IsAlgebraicSpace B S hS (V₀.preimage r).toFunctor)
    (hW : IsAlgebraicSpace B S hS ((F.U i ⊓ F.U j).preimage r).toFunctor)
    (hUW : V₀.preimage r ≤ (F.U i ⊓ F.U j).preimage r) :
    IsomFamily B S hS (V₀.preimage r).toFunctor hU
      (algebraicSpaceStackMap.{u, w} B S hS hU hW (Subfunctor.homOfLe hUW) ≫
        algebraicSpaceStackMap.{u, w} B S hS hW (F.isOpen_inf i j).1
          ((F.U i ⊓ F.U j).fromPreimage r) ≫ F.left i j)
      (algebraicSpaceStackMap.{u, w} B S hS hU hW (Subfunctor.homOfLe hUW) ≫
        algebraicSpaceStackMap.{u, w} B S hS hW (F.isOpen_inf i j).1
          ((F.U i ⊓ F.U j).fromPreimage r) ≫ F.right i j) :=
  ψ.restrict hU (V₀.fromPreimage r)

/-- The value of `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.isosPreimage` at a
point of `r⁻¹(V₀)` is the value of `ψ` at its image. -/
theorem isosPreimage_apply (F : SectionFamily hY f W hY₀ q₀ ι) {V₀ : Subfunctor Y₀}
    (hV₀ : Space.IsOpenSubspace B S hS V₀) (hVU : ∀ i, V₀ ≤ F.U i) {i j : ι}
    (ψ : IsomFamily B S hS V₀.toFunctor hV₀.1
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen i).1 (Subfunctor.homOfLe (hVU i)) ≫
        F.x i)
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen j).1 (Subfunctor.homOfLe (hVU j)) ≫
        F.x j))
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : Y₁ ⟶ Y₀)
    (hU : IsAlgebraicSpace B S hS (V₀.preimage r).toFunctor)
    (hW : IsAlgebraicSpace B S hS ((F.U i ⊓ F.U j).preimage r).toFunctor)
    (hUW : V₀.preimage r ≤ (F.U i ⊓ F.U j).preimage r) (T : (BigFppfOver B S hS)ᵒᵖ)
    (v : Y₁.obj T) (hv : v ∈ (V₀.preimage r).obj T) :
    (F.isosPreimage hV₀ hVU ψ r hU hW hUW).1 T ⟨v, hv⟩ = ψ.1 T ⟨r.app T v, hv⟩ :=
  rfl

/-- **One pair at a time** (the step `(f) → (g)` of the proof of Stacks 0CQ7, for one pair).
Over a quasi-compact quasi-separated `Y₁` proper over `Y₀`, the section of the proper
`Isom(x i, x j) ⟶ r⁻¹(U i ∩ U j)` named by `ψ` over `r⁻¹(V₀)` extends, after an
`r⁻¹(V₀)`-admissible blowup `b`, to `b⁻¹ r⁻¹(U i ∩ U j)` (Stacks 0CPI). -/
theorem exists_hasIsoExtension_step
    (h0CPI : ∀ {X Y : AlgebraicSpaces B S hS}
      (_hYqc : Space.IsQuasiCompactSpace B S hS Y.1)
      (_hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
      (U W : Space.OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1)
      (_hUqc : Space.IsQuasiCompactSpace B S hS U.1.toFunctor)
      (_hWqc : Space.IsQuasiCompactSpace B S hS W.1.toFunctor)
      (f : X ⟶ Space.openSubspace B S hS Y W) (_hf : Space.IsProper B S hS f.hom)
      (s : U.1.toFunctor ⟶ X.1) (_hs : s ≫ f.hom = Subfunctor.homOfLe hUW),
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), Space.IsAdmissibleBlowup B S hS U b ∧
        ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1, s' ≫ f.hom = W.1.fromPreimage b.hom ∧
          Subfunctor.homOfLe (fun T _ hx => hUW T hx :
            U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' = U.1.fromPreimage b.hom ≫ s)
    (hproper : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳), x₁ ≫ f = x₂ ≫ f →
      Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂))
    (F : SectionFamily hY f W hY₀ q₀ ι)
    (hY₀qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀)
    {V₀ : Subfunctor Y₀} (hV₀ : Space.IsOpenSubspace B S hS V₀)
    (hV₀qc : Space.IsQuasiCompactSpace B S hS V₀.toFunctor) (hVU : ∀ i, V₀ ≤ F.U i) {i j : ι}
    (ψ : IsomFamily B S hS V₀.toFunctor hV₀.1
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen i).1 (Subfunctor.homOfLe (hVU i)) ≫
        F.x i)
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen j).1 (Subfunctor.homOfLe (hVU j)) ≫
        F.x j))
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀)
    (hr : Space.IsProper B S hS r) (hY₁qc : Space.IsQuasiCompactSpace B S hS Y₁)
    (hY₁qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁) :
    ∃ (Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY₂ : IsAlgebraicSpace B S hS Y₂) (b : Y₂ ⟶ Y₁),
      Space.IsProper B S hS b ∧ Space.IsQuasiCompactSpace B S hS Y₂ ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₂ ∧
      Set.range (Space.pointsMap B S hS (V₀.preimage r).toFunctor (V₀.preimage r).ι) ⊆
        Space.pointsMap B S hS Y₂ b '' Set.range (Space.pointsMap B S hS
          ((V₀.preimage r).preimage b).toFunctor ((V₀.preimage r).preimage b).ι) ∧
      F.HasIsoExtension hV₀ hVU ψ hY₂ (b ≫ r) := by
  let := hasSheafify_bigFppfOver B S hS
  have hUo := Space.isOpenSubspace_preimage B S hS r V₀ hY₀ hY₁ hV₀
  have hWo := Space.isOpenSubspace_preimage B S hS r _ hY₀ hY₁ (F.isOpen_inf i j)
  have hUW : V₀.preimage r ≤ (F.U i ⊓ F.U j).preimage r := fun T v hv => ⟨hVU i T hv, hVU j T hv⟩
  have hUqc : Space.IsQuasiCompactSpace B S hS (V₀.preimage r).toFunctor :=
    Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₀ hY₁ r hr.2.1.2 hV₀ hV₀qc
  have hWqc : Space.IsQuasiCompactSpace B S hS ((F.U i ⊓ F.U j).preimage r).toFunctor :=
    Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₀ hY₁ r hr.2.1.2
      (F.isOpen_inf i j)
      (Space.isQuasiCompactSpace_inf_of_isAbsolutelyQuasiSeparated B S hS hY₀ hY₀qs
        (F.isOpen i) (F.isOpen j) (F.isQC i) (F.isQC j))
  have hprop := hproper _ hWo.1
    (algebraicSpaceStackMap.{u, w} B S hS hWo.1 (F.isOpen_inf i j).1
      ((F.U i ⊓ F.U j).fromPreimage r) ≫ F.left i j)
    (algebraicSpaceStackMap.{u, w} B S hS hWo.1 (F.isOpen_inf i j).1
      ((F.U i ⊓ F.U j).fromPreimage r) ≫ F.right i j)
    (by rw [Category.assoc, Category.assoc, F.left_comp_eq_right_comp])
  obtain ⟨Y₂, b, hb, φ, hφ⟩ := IsomFamily.exists_isAdmissibleBlowup_extension h0CPI hY₁ hY₁qc
    hY₁qs ⟨_, hUo⟩ ⟨_, hWo⟩ hUW hUqc hWqc _ _ hprop (F.isosPreimage hV₀ hVU ψ r hUo.1 hWo.1 hUW)
  have hbp : Space.IsProper B S hS b.hom := hb.isProper
  obtain ⟨hqc₂, hqs₂⟩ := Space.isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper
    B S hS Y₂.2 hY₁ b.hom hbp hY₁qc hY₁qs
  exact ⟨Y₂.1, Y₂.2, b.hom, hbp, hqc₂, hqs₂,
    Space.IsAdmissibleBlowup.range_subset_image_range_preimage hb, φ, fun T v hv =>
      (hφ T v hv).trans (F.isosPreimage_apply hV₀ hVU ψ r hUo.1 hWo.1 hUW T _ hv)⟩

end SectionFamily

/-- **Extending the isomorphisms of the proof of Stacks 0CQ7 from `V₀` to the intersections**
(step `(f) → (g)` of that proof). Let `F` be a family of local sections `x i : U i ⟶ 𝒳` over a
quasi-compact quasi-separated `Y₀`, and `ψ i j` isomorphisms between `x i` and `x j` over a
quasi-compact open `V₀ ⊆ ⋂ U i` satisfying the cocycle condition. Then there is a proper
`r : Y₁ ⟶ Y₀`, with `Y₁` quasi-compact and quasi-separated and `r⁻¹(V₀)` covering the points of
`V₀`, and isomorphisms `φ i j` between the pullbacks of `x i` and `x j` over all of
`r⁻¹(U i ∩ U j)` whose cocycle condition holds over `r⁻¹(V₀)`.

The isomorphism spaces `Isom(x i, x j) ⟶ U i ∩ U j` are proper (`hproper`, as `f` is
separated), `ψ i j` is a section of it over `V₀`, and Stacks 0CPI (`h0CPI`) extends it after a
`V₀`-admissible blowup; the blowups are done one pair at a time, each over the previous one,
and the already extended isomorphisms are restricted. Over `r⁻¹(V₀)` every `φ i j` is the
pullback of `ψ i j`, so the cocycle condition is that of `ψ`. -/
theorem SectionFamily.exists_isos_of_isosOn
    (h0CPI : ∀ {X Y : AlgebraicSpaces B S hS}
      (_hYqc : Space.IsQuasiCompactSpace B S hS Y.1)
      (_hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
      (U W : Space.OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1)
      (_hUqc : Space.IsQuasiCompactSpace B S hS U.1.toFunctor)
      (_hWqc : Space.IsQuasiCompactSpace B S hS W.1.toFunctor)
      (f : X ⟶ Space.openSubspace B S hS Y W) (_hf : Space.IsProper B S hS f.hom)
      (s : U.1.toFunctor ⟶ X.1) (_hs : s ≫ f.hom = Subfunctor.homOfLe hUW),
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), Space.IsAdmissibleBlowup B S hS U b ∧
        ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1, s' ≫ f.hom = W.1.fromPreimage b.hom ∧
          Subfunctor.homOfLe (fun T _ hx => hUW T hx :
            U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' = U.1.fromPreimage b.hom ≫ s)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
    (hproper : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳), x₁ ≫ f = x₂ ≫ f →
      Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂))
    {W : Subfunctor Y} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀}
    {q₀ : Y₀ ⟶ Y} {ι : Type} [Finite ι]
    (F : SectionFamily hY f W hY₀ q₀ ι) (hY₀qc : Space.IsQuasiCompactSpace B S hS Y₀)
    (hY₀qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀)
    (V₀ : Subfunctor Y₀) (hV₀ : Space.IsOpenSubspace B S hS V₀)
    (hV₀qc : Space.IsQuasiCompactSpace B S hS V₀.toFunctor) (hVU : ∀ i, V₀ ≤ F.U i)
    (ψ : ∀ i j, IsomFamily B S hS V₀.toFunctor hV₀.1
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen i).1 (Subfunctor.homOfLe (hVU i)) ≫
        F.x i)
      (algebraicSpaceStackMap.{u, w} B S hS hV₀.1 (F.isOpen j).1 (Subfunctor.homOfLe (hVU j)) ≫
        F.x j))
    (hcoc : ∀ i j k T v, (ψ i j).1 T v ≫ (ψ j k).1 T v = (ψ i k).1 T v) :
    ∃ (Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀)
      (hr : Space.IsProper B S hS r),
      Space.IsQuasiCompactSpace B S hS Y₁ ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁ ∧
      Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) ⊆
        Space.pointsMap B S hS Y₁ r '' Set.range
          (Space.pointsMap B S hS (V₀.preimage r).toFunctor (V₀.preimage r).ι) ∧
      ∃ (hVU' : ∀ i, V₀.preimage r ≤ (F.restrict hY₁ r hr.2.1.2).U i)
        (φ : ∀ i j, (F.restrict hY₁ r hr.2.1.2).Isos i j),
        ∀ i j k (T : (BigFppfOver B S hS)ᵒᵖ) (v : Y₁.obj T) (hv : v ∈ (V₀.preimage r).obj T),
          (φ i j).1 T ⟨v, hVU' i T hv, hVU' j T hv⟩ ≫ (φ j k).1 T ⟨v, hVU' j T hv, hVU' k T hv⟩ =
            (φ i k).1 T ⟨v, hVU' i T hv, hVU' k T hv⟩ := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ L : List (ι × ι), ∃ (Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀), Space.IsProper B S hS r ∧
      Space.IsQuasiCompactSpace B S hS Y₁ ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁ ∧
      Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) ⊆
        Space.pointsMap B S hS Y₁ r '' Set.range
          (Space.pointsMap B S hS (V₀.preimage r).toFunctor (V₀.preimage r).ι) ∧
      ∀ p ∈ L, F.HasIsoExtension hV₀ hVU (ψ p.1 p.2) hY₁ r := by
    intro L
    induction L with
    | nil =>
      refine ⟨Y₀, hY₀, 𝟙 Y₀, Space.isProper_of_isIso B S hS _, hY₀qc, hY₀qs, ?_, by simp⟩
      intro x hx
      refine ⟨x, ?_, by rw [Space.pointsMap_id]; rfl⟩
      rw [Space.range_pointsMap_preimage_ι, Space.pointsMap_id]
      exact hx
    | cons p L ih =>
      obtain ⟨Y₁, hY₁, r, hr, hqc, hqs, hlift, hL⟩ := ih
      obtain ⟨Y₂, hY₂, b, hb, hqc₂, hqs₂, hliftb, hext⟩ :=
        SectionFamily.exists_hasIsoExtension_step h0CPI hproper F hY₀qs hV₀ hV₀qc hVU
          (ψ p.1 p.2) hY₁ r hr hqc hqs
      refine ⟨Y₂, hY₂, b ≫ r, Space.isProper_comp B S hS hY₂ hY₁ hY₀ b r hb hr, hqc₂, hqs₂,
        ?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := hlift hx
        obtain ⟨z, hz, rfl⟩ := hliftb hy
        exact ⟨z, hz, by rw [Space.pointsMap_comp_apply]⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hext
        · exact (hL q hq).comp hY₂ b
  obtain ⟨Y₁, hY₁, r, hr, hqc, hqs, hlift, hL⟩ := key (Finset.univ : Finset (ι × ι)).toList
  have hext : ∀ i j, F.HasIsoExtension hV₀ hVU (ψ i j) hY₁ r := fun i j =>
    hL (i, j) (by simp)
  unfold SectionFamily.HasIsoExtension at hext
  choose φ hφ using hext
  refine ⟨Y₁, hY₁, r, hr, hqc, hqs, hlift, fun i T v hv => hVU i T hv, φ, ?_⟩
  intro i j k T v hv
  have h := hcoc i j k T ⟨r.app T v, hv⟩
  rw [← hφ i j T v hv, ← hφ j k T v hv, ← hφ i k T v hv] at h
  exact h

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
