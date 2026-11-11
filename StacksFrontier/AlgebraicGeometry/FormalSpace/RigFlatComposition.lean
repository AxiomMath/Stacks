module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.RingTheory.Rig.FlatStableUnderComposition

/-!
# Rig-flatness is stable under composition

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GH0** says that if
`f` and `g` are rig-flat (Stacks 0GGX), then so is `g ∘ f`. Rig-flatness of `f` is a condition
on every commutative square

```
U ⟶ V
↓     ↓
X ⟶ Y
```

whose verticals are affine étale charts (Stacks 0GGX), so a composite `X ⟶ Y ⟶ Z` presents a
square with no chart of the intermediate space `Y` in it.

Beside Stacks 0GH0 the file threads the ring-level composition law of Stacks 0GGV through
explicit chart data: given charts of all three spaces fitting into two squares, the continuous
homomorphism realizing the composed chart morphism is rig-flat. Making that statement about an
*arbitrary* continuous homomorphism realizing the composed chart morphism requires knowing that
such a homomorphism is the composite of the two given ones. That follows from Stacks 0AN0, once
continuous homomorphisms over the base can be composed at all; `ContinuousHom.comp` supplies the
latter, which the library was missing even though the composition law for formal spectra
(`formalSpectrumMap_comp`) asks for it as an input.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ContinuousHom.comp`: composition of continuous homomorphisms
  of topological rings over the base.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigFlat_comp`: the composition law of Stacks 0GH0 for
  arbitrary fppf sheaves, from the uniform transfer `TransfersCompositionOnAffineEtaleDiagrams`.
* `AlgebraicGeometry.FormalSpace.isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`: Definition
  0GGX is condition (1) of Stacks 0ANG for rig-flatness as a property of arrows of `WAdm^Noeth`.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_comp_eq`: `Spf` turns `ContinuousHom.comp`
  into composition, a usable form of **Stacks 0AIF**.
* `AlgebraicGeometry.FormalSpace.IsRigFlat.rigFlat_comp_of_charts`: the composite of the two
  realizing homomorphisms of two chart squares over rig-flat morphisms is rig-flat.
* `AlgebraicGeometry.FormalSpace.IsRigFlat.rigFlat_of_charts`: the same for any continuous
  homomorphism realizing the composed chart morphism.

## Implementation notes

Stacks 0GH0 is the composite of two facts. At the level of topological rings, rig-flatness is
stable under composition in the sense of Remark 0GBK; this is Stacks 0GGV, carried by the
library as `Rig.rigFlat_isStableUnderCompositionNoetherian`, whose locality input (Stacks 0GGU)
is proved. Remark 0GBK then draws from such a stability bundle the geometric transfer:
condition (1) of Stacks 0ANG passes from `f` and `g` to their composite. For locally Noetherian
formal algebraic spaces that transfer is proved, as
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian`,
and Stacks 0GH0 itself is
`AlgebraicGeometry.FormalSpace.isRigFlat_comp_of_isLocallyNoetherian` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatCompositionLocallyNoetherian`.

`isRigFlat_comp` here is the same composition for arbitrary fppf sheaves `X`, `Y`, `Z`, with no
locally Noetherian hypothesis; it takes the uniform transfer
`TransfersCompositionOnAffineEtaleDiagrams`, quantified over *all* properties admitting a
stability bundle, which is the arrangement of the rig-smooth variant Stacks 0GCS in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothComposition`, from which the hypothesis is
imported. What the file itself supplies is the passage between the predicate of Stacks 0GGX
and that machinery, in both directions, together with the instantiation of the generic transfer
at the rig-flat property furnished by Stacks 0GGV.

In `isRigFlat_comp` the rings over which the chart condition quantifies are adic Noetherian,
exactly as for Stacks 0GGX; the sheaves `X`, `Y`, `Z` themselves carry no hypothesis.

Composability of continuous homomorphisms is not formal: the `overS` field has to be checked on
every pair of weak ideals of definition `J` of the source and `K` of the target with
`J ⊆ (q ∘ r)^{-1} K`, and the two given homomorphisms only provide such data for ideals chosen
by continuity. The proof interposes a weak ideal of definition `J₂` of the middle ring inside
`q^{-1} K`, pulls it back to a weak ideal of definition inside `r^{-1} J₂`, intersects that with
`J`, and uses the compatibility of the quotient systems to descend `J` to the intersection;
weak admissibility of the middle and source rings is what makes those choices possible, and is
therefore a hypothesis of `ContinuousHom.comp`.

`IsRigFlat.rigFlat_of_charts` carries affineness of the chart `W` only, which is what Stacks
0GGX consumes; Stacks 0AN0 identifies the continuous homomorphism realizing the composite
without any affineness hypothesis on `formalSpectrum D₃`.

## References

* [Stacks Project, Tag 0GH0](https://stacks.math.columbia.edu/tag/0GH0)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GGV](https://stacks.math.columbia.edu/tag/0GGV)
* [Stacks Project, Tag 0GGX](https://stacks.math.columbia.edu/tag/0GGX)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
  [TopologicalSpace A₁] [TopologicalSpace A₂] [TopologicalSpace A₃]

/-- A continuous ring map admits a weak ideal of definition of its source inside the preimage
of any weak ideal of definition of its target, as soon as the source is weakly pre-admissible.
-/
theorem exists_isWeakIdealOfDefinition_le_comap
    (hw : TopologicalRing.IsWeaklyPreAdmissible A₂) (φ : A₂ →+* A₁) (hφ : Continuous φ)
    (K : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ∃ J : { I : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ Ideal.comap φ K.1 := by
  obtain ⟨I, hI⟩ := hw
  exact ⟨⟨I ⊓ Ideal.comap φ K.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hI
      (K.2.1.preimage hφ)⟩, inf_le_right⟩

section Comp

variable [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂]
  [IsTopologicalRing A₃] [IsLinearTopology A₃ A₃]
  {D₁ : QuotientSystem B S hS A₁} {D₂ : QuotientSystem B S hS A₂}
  {D₃ : QuotientSystem B S hS A₃}

/-- The composition of two continuous homomorphisms of topological rings over the base. -/
def ContinuousHom.comp (hw₂ : TopologicalRing.IsWeaklyAdmissible A₂)
    (hw₃ : TopologicalRing.IsWeaklyAdmissible A₃)
    (q : ContinuousHom D₂ D₁) (r : ContinuousHom D₃ D₂) : ContinuousHom D₃ D₁ where
  toRingHom := q.toRingHom.comp r.toRingHom
  continuous := q.continuous.comp r.continuous
  overS J K h := by
    obtain ⟨J₂, hJ₂⟩ :=
      exists_isWeakIdealOfDefinition_le_comap hw₂.1 q.toRingHom q.continuous K
    obtain ⟨J₃, hJ₃⟩ :=
      exists_isWeakIdealOfDefinition_le_comap hw₃.1 r.toRingHom r.continuous J₂
    let M : { I : Ideal A₃ // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨J.1 ⊓ J₃.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 J₃.2.1⟩
    have hMJ : M.1 ≤ J.1 := inf_le_left
    have hMJ₂ : M.1 ≤ Ideal.comap r.toRingHom J₂.1 := inf_le_right.trans hJ₃
    have he : (Ideal.quotientMap K.1 (q.toRingHom.comp r.toRingHom) h).comp
          (Ideal.Quotient.factor hMJ) =
        (Ideal.quotientMap K.1 q.toRingHom hJ₂).comp
          (Ideal.quotientMap J₂.1 r.toRingHom hMJ₂) := by
      refine Ideal.Quotient.ringHom_ext ?_
      ext a
      rfl
    calc Spec.map (CommRingCat.ofHom
          (Ideal.quotientMap K.1 (q.toRingHom.comp r.toRingHom) h)) ≫ D₃.overS J
        = Spec.map (CommRingCat.ofHom
              (Ideal.quotientMap K.1 (q.toRingHom.comp r.toRingHom) h)) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMJ)) ≫ D₃.overS M := by
          rw [D₃.compatible M J hMJ]
      _ = Spec.map (CommRingCat.ofHom
              ((Ideal.quotientMap K.1 (q.toRingHom.comp r.toRingHom) h).comp
                (Ideal.Quotient.factor hMJ))) ≫ D₃.overS M := by
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = Spec.map (CommRingCat.ofHom ((Ideal.quotientMap K.1 q.toRingHom hJ₂).comp
              (Ideal.quotientMap J₂.1 r.toRingHom hMJ₂))) ≫ D₃.overS M := by
          rw [he]
      _ = Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 q.toRingHom hJ₂)) ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.quotientMap J₂.1 r.toRingHom hMJ₂)) ≫ D₃.overS M := by
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 q.toRingHom hJ₂)) ≫
            D₂.overS J₂ := by rw [r.overS M J₂ hMJ₂]
      _ = D₁.overS K := q.overS J₂ K hJ₂

@[simp]
theorem ContinuousHom.comp_toRingHom (hw₂ : TopologicalRing.IsWeaklyAdmissible A₂)
    (hw₃ : TopologicalRing.IsWeaklyAdmissible A₃)
    (q : ContinuousHom D₂ D₁) (r : ContinuousHom D₃ D₂) :
    (ContinuousHom.comp hw₂ hw₃ q r).toRingHom = q.toRingHom.comp r.toRingHom :=
  rfl

/-- **Stacks 0AIF.** The formal spectrum turns `ContinuousHom.comp` into composition of
morphisms of formal spectra, in the direction that reverses the order. -/
@[stacks 0AIF "composition law for the composite continuous hom"]
theorem formalSpectrumMap_comp_eq (hw₂ : TopologicalRing.IsWeaklyAdmissible A₂)
    (hw₃ : TopologicalRing.IsWeaklyAdmissible A₃)
    (q : ContinuousHom D₂ D₁) (r : ContinuousHom D₃ D₂) :
    formalSpectrumMap hw₂ q ≫ formalSpectrumMap hw₃ r =
      formalSpectrumMap hw₃ (ContinuousHom.comp hw₂ hw₃ q r) :=
  formalSpectrumMap_comp hw₃ hw₂ r q (ContinuousHom.comp hw₂ hw₃ q r) rfl

end Comp

section Charts

variable [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁] [IsNoetherianRing A₁]
  [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂] [IsNoetherianRing A₂]
  [IsTopologicalRing A₃] [IsLinearTopology A₃ A₃] [IsNoetherianRing A₃]
  {X Y Z : FppfSheaf B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Two chart squares over rig-flat morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` compose: the
composite of the continuous homomorphisms realizing the two chart morphisms is rig-flat. This
is Stacks 0GGV read on charts; see the module docstring for why it is not Stacks 0GH0. -/
theorem IsRigFlat.rigFlat_comp_of_charts
    (hf : IsRigFlat B S hS f) (hg : IsRigFlat B S hS g)
    (U V W : FppfSheaf B S hS)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hW : IsAffineFormalAlgebraicSpace B S hS W)
    (a : U ⟶ X) (b : V ⟶ Y) (c : W ⟶ Z) (t : U ⟶ V) (s : V ⟶ W)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom)
    (hb : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS b.hom)
    (hc : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom)
    (hae : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ m ↦ Space.IsEtaleULift.{u + 1} B S hS m.hom) a.hom ha)
    (hbe : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ m ↦ Space.IsEtaleULift.{u + 1} B S hS m.hom) b.hom hb)
    (hce : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ m ↦ Space.IsEtaleULift.{u + 1} B S hS m.hom) c.hom hc)
    (hsq : a ≫ f = t ≫ b) (hsq' : b ≫ g = s ≫ c)
    (hA₁ : TopologicalRing.IsAdic A₁) (hA₂ : TopologicalRing.IsAdic A₂)
    (hA₃ : TopologicalRing.IsAdic A₃)
    (hw₂ : TopologicalRing.IsWeaklyAdmissible A₂)
    (hw₃ : TopologicalRing.IsWeaklyAdmissible A₃)
    (D₁ : QuotientSystem B S hS A₁) (D₂ : QuotientSystem B S hS A₂)
    (D₃ : QuotientSystem B S hS A₃)
    (eU : U ≅ formalSpectrum D₁) (eV : V ≅ formalSpectrum D₂) (eW : W ≅ formalSpectrum D₃)
    (q : ContinuousHom D₂ D₁) (r : ContinuousHom D₃ D₂)
    (ht : t = eU.hom ≫ formalSpectrumMap hw₂ q ≫ eV.inv)
    (hs : s = eV.hom ≫ formalSpectrumMap hw₃ r ≫ eW.inv) :
    Rig.RingHom.IsRigFlat (q.toRingHom.comp r.toRingHom) :=
  Rig.rigFlat_isStableUnderCompositionNoetherian.comp
    ⟨hA₁, inferInstance⟩ ⟨hA₂, inferInstance⟩ ⟨hA₃, inferInstance⟩
    q.toRingHom r.toRingHom q.continuous r.continuous
    (hf U V hU hV a b t ha hb hae hbe hsq A₂ A₁ hA₂ hA₁ hw₂ D₂ D₁ eU eV q ht)
    (hg V W hV hW b c s hb hc hbe hce hsq' A₃ A₂ hA₃ hA₂ hw₃ D₃ D₂ eV eW r hs)

/-- The form of `AlgebraicGeometry.FormalSpace.IsRigFlat.rigFlat_comp_of_charts` that Stacks
0GH0 needs: *any* continuous homomorphism realizing the composed chart morphism `U ⟶ W` is
rig-flat. Stacks 0AN0 identifies it with the composite of the two given ones. -/
theorem IsRigFlat.rigFlat_of_charts
    (hf : IsRigFlat B S hS f) (hg : IsRigFlat B S hS g)
    (U V W : FppfSheaf B S hS)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hW : IsAffineFormalAlgebraicSpace B S hS W)
    (a : U ⟶ X) (b : V ⟶ Y) (c : W ⟶ Z) (t : U ⟶ V) (s : V ⟶ W)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom)
    (hb : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS b.hom)
    (hc : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom)
    (hae : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ m ↦ Space.IsEtaleULift.{u + 1} B S hS m.hom) a.hom ha)
    (hbe : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ m ↦ Space.IsEtaleULift.{u + 1} B S hS m.hom) b.hom hb)
    (hce : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ m ↦ Space.IsEtaleULift.{u + 1} B S hS m.hom) c.hom hc)
    (hsq : a ≫ f = t ≫ b) (hsq' : b ≫ g = s ≫ c)
    (hA₁ : TopologicalRing.IsAdic A₁) (hA₂ : TopologicalRing.IsAdic A₂)
    (hA₃ : TopologicalRing.IsAdic A₃)
    (hw₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    (hw₂ : TopologicalRing.IsWeaklyAdmissible A₂)
    (hw₃ : TopologicalRing.IsWeaklyAdmissible A₃)
    (D₁ : QuotientSystem B S hS A₁) (D₂ : QuotientSystem B S hS A₂)
    (D₃ : QuotientSystem B S hS A₃)
    (eU : U ≅ formalSpectrum D₁) (eV : V ≅ formalSpectrum D₂) (eW : W ≅ formalSpectrum D₃)
    (q : ContinuousHom D₂ D₁) (r : ContinuousHom D₃ D₂) (h : ContinuousHom D₃ D₁)
    (ht : t = eU.hom ≫ formalSpectrumMap hw₂ q ≫ eV.inv)
    (hs : s = eV.hom ≫ formalSpectrumMap hw₃ r ≫ eW.inv)
    (hh : t ≫ s = eU.hom ≫ formalSpectrumMap hw₃ h ≫ eW.inv) :
    Rig.RingHom.IsRigFlat h.toRingHom := by
  have hmap : formalSpectrumMap hw₃ h =
      formalSpectrumMap hw₃ (ContinuousHom.comp hw₂ hw₃ q r) := by
    rw [← formalSpectrumMap_comp_eq hw₂ hw₃ q r]
    have hcancel : eU.hom ≫ formalSpectrumMap hw₃ h ≫ eW.inv =
        eU.hom ≫ (formalSpectrumMap hw₂ q ≫ formalSpectrumMap hw₃ r) ≫ eW.inv := by
      rw [← hh, ht, hs]
      simp [Category.assoc]
    have h' := (Iso.cancel_iso_hom_left eU _ _).mp hcancel
    exact (Iso.cancel_iso_inv_right _ _ eW).mp h'
  have heq : h = ContinuousHom.comp hw₂ hw₃ q r :=
    ((existsUnique_continuousHom_formalSpectrumMap_eq hw₃ hw₁
      (formalSpectrumMap hw₃ h)).unique rfl hmap.symm)
  rw [heq, ContinuousHom.comp_toRingHom]
  exact IsRigFlat.rigFlat_comp_of_charts hf hg U V W hU hV hW a b c t s ha hb hc hae hbe hce
    hsq hsq' hA₁ hA₂ hA₃ hw₂ hw₃ D₁ D₂ D₃ eU eV eW q r ht hs

end Charts

section Composition

variable {X Y Z : FppfSheaf B S hS}

/-- Definition 0GGX is condition (1) of **Stacks 0ANG** for rig-flatness read as a property of
arrows of `WAdm^Noeth`: a morphism of formal algebraic spaces over `S` is rig-flat exactly when
every affine étale diagram over it carries a rig-flat continuous homomorphism. -/
theorem isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram (f : X ⟶ Y) :
    IsRigFlat B S hS f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
        (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
          [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
          Rig.RingHom.IsRigFlat φ) f := by
  constructor
  · intro h U V a b t hU hV ⟨ha, haet⟩ ⟨hb, hbet⟩ hcomm A R _ _ _ _ _ _ _ _
      ⟨hAadic, hAnoeth⟩ ⟨hRadic, hRnoeth⟩ hA D E eU eV g hg
    exact h U V hU hV a b t ha hb haet hbet hcomm A R hAadic hRadic hA D E eU eV g hg
  · intro h U V hU hV a b t ha hb haet hbet hcomm A R _ _ _ _ _ _ _ _ _ _
      hAadic hRadic hA D E eU eV g hg
    exact h U V a b t hU hV ⟨ha, haet⟩ ⟨hb, hbet⟩ hcomm A R
      ⟨hAadic, inferInstance⟩ ⟨hRadic, inferInstance⟩ hA D E eU eV g hg

/-- A composite of rig-flat morphisms of fppf sheaves over `S` is rig-flat, given the uniform
transfer `TransfersCompositionOnAffineEtaleDiagrams` of condition (1) of Stacks 0ANG along
composition. For locally Noetherian formal algebraic spaces, the setting of Stacks 0GH0, no such
transfer is needed: see `AlgebraicGeometry.FormalSpace.isRigFlat_comp_of_isLocallyNoetherian`. -/
theorem isRigFlat_comp (htransfer : TransfersCompositionOnAffineEtaleDiagrams B S hS)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsRigFlat B S hS f) (hg : IsRigFlat B S hS g) :
    IsRigFlat B S hS (f ≫ g) :=
  (isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram (f ≫ g)).mpr
    (htransfer _ Rig.rigFlat_isStableUnderCompositionNoetherian f g
      ((isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram f).mp hf)
      ((isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram g).mp hg))

end Composition

end AlgebraicGeometry.FormalSpace

end
