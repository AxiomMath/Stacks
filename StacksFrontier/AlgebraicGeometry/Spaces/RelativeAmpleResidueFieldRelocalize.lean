module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldOpens

/-!
# Claim (A) of Stacks 0D3D over a larger base gives it over a smaller one

Let `h : W ⟶ S` be a morphism of a big fppf site. The residue-field form of claim (A) of the
proof of Stacks 0D3D, `AlgebraicGeometry.Space.AmpleSpreadsFromResidueFieldsToOpens`, over `S`
implies it over `W`: a proper morphism `X' ⟶ h_U` over `W`, with its invertible module, is
viewed over `S` by the lower-shriek extension `Λ`, with the module read across the equivalence of
small étale sites (`AlgebraicGeometry.Space.moduleRelocalizeEquivalence`); the hypothesis at the
residue field and the conclusion over an open of `U` are statements about base changes of the
same schemes, and relative ampleness of the module does not depend on the base
(`AlgebraicGeometry.Space.isRelativelyAmple_moduleDerelocalize_iff`).

The source works with algebraic spaces over `ℤ` at this point of the proof ("`Y_i` of finite
presentation over `ℤ`"); this is the passage from `S` to `ℤ`, with `S` taken to be the terminal
scheme.

## Main results

* `Space.ampleSpreadsFromResidueFieldsToOpens_of_relocalize`: the transport.
* `Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleSpreadsOverIntegers`:
  the conclusion of Stacks 0D3D over any base `S`, from the fpqc case of Stacks 0D3C over `S`
  and the residue-field form of claim (A) over `Spec ℤ`.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}

/-- **Ampleness on a base change does not depend on the chosen square, nor on an isomorphism of
the base.** If the pullback of `L` is ample on one base change of `F` along `e ≫ g'` with `e`
an isomorphism, it is ample on every base change of `F` along `g'`. -/
theorem isRelativelyAmple_of_isPullback_of_isIso {X Z Y₀ Y₀' X₀ X₀' : AlgebraicSpaces B S hS}
    {F : X ⟶ Z} {g' : Y₀' ⟶ Z} (e : Y₀ ≅ Y₀') {p : X₀ ⟶ X} {f₀ : X₀ ⟶ Y₀}
    {p' : X₀' ⟶ X} {f₀' : X₀' ⟶ Y₀'} {L : Modules.{u, u} B S hS X.1 X.2}
    (hsq₁ : IsPullback p f₀ F (e.hom ≫ g'))
    (h₁ : IsRelativelyAmple B S hS f₀ ((modulePullback B S hS p).obj L))
    (hsq₂ : IsPullback p' f₀' F g') :
    IsRelativelyAmple B S hS f₀' ((modulePullback B S hS p').obj L) := by
  let c : X₀' ⟶ X₀ := hsq₁.lift p' (f₀' ≫ e.inv) (by simpa using hsq₂.w)
  have hcp : c ≫ p = p' := hsq₁.lift_fst _ _ _
  have hcf : c ≫ f₀ = f₀' ≫ e.inv := hsq₁.lift_snd _ _ _
  have hsqc : IsPullback c f₀' f₀ e.inv :=
    IsPullback.of_right (by rw [hcp, Iso.inv_hom_id_assoc]; exact hsq₂) hcf hsq₁
  have h := isRelativelyAmple_baseChange hsqc _ h₁
  rw [← hcp]
  exact (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS c p).app L)).mp h

variable (h : B.obj hW ⟶ B.obj hS)

/-- `Λ` carries cartesian squares of algebraic spaces to cartesian squares. -/
theorem isPullback_relocalizeSpaceMap {P X Y Z : AlgebraicSpaces B W hW} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hsq : IsPullback fst snd f g) :
    IsPullback (relocalizeSpaceMap h fst) (relocalizeSpaceMap h snd) (relocalizeSpaceMap h f)
      (relocalizeSpaceMap h g) := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  refine IsPullback.of_map (ObjectProperty.ι _) ?_
    ((AlgebraicSpaces.isPullback_hom B W hW hsq).map (OverShriek.relocalizePresheafFunctor h))
  ext1
  change (OverShriek.relocalizePresheafFunctor h).map fst.hom ≫
      (OverShriek.relocalizePresheafFunctor h).map f.hom =
    (OverShriek.relocalizePresheafFunctor h).map snd.hom ≫
      (OverShriek.relocalizePresheafFunctor h).map g.hom
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (congrArg (fun k => k.hom) hsq.w)

/-- The relocalization of the algebraic space represented by `A` is represented by `Λ A`. -/
def relocalizeRepresentedIso (A : BigFppfOver B W hW) :
    relocalizeSpace B hW hS h (representedAlgebraicSpace B W hW A) ≅
      representedAlgebraicSpace B S hS ((Over.map h).obj A) :=
  ObjectProperty.isoMk _ (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h A)

/-- `relocalizeRepresentedIso` is natural in the represented object. -/
theorem relocalizeRepresentedIso_naturality {A A' : BigFppfOver B W hW} (a : A ⟶ A') :
    relocalizeSpaceMap h (ObjectProperty.homMk (yoneda.map a) :
        representedAlgebraicSpace B W hW A ⟶ representedAlgebraicSpace B W hW A') ≫
        (relocalizeRepresentedIso h A').hom =
      (relocalizeRepresentedIso h A).hom ≫
        ObjectProperty.homMk (yoneda.map ((Over.map h).map a)) := by
  ext1
  exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h a

/-- The relocalization of a represented algebraic space, identified with a given object over
`S` isomorphic to the relocalized object. -/
def relocalizeRepresentedIsoOfIso {A : BigFppfOver B W hW} {A' : BigFppfOver B S hS}
    (α : (Over.map h).obj A ≅ A') :
    relocalizeSpace B hW hS h (representedAlgebraicSpace B W hW A) ≅
      representedAlgebraicSpace B S hS A' :=
  relocalizeRepresentedIso h A ≪≫ ObjectProperty.isoMk _ (yoneda.mapIso α)

/-- Relocalizing the morphism of represented spaces induced by `a`, followed by
`relocalizeRepresentedIso`, is `relocalizeRepresentedIsoOfIso h α` followed by the morphism
induced by `a'`, whenever `α.hom ≫ a' = (Over.map h).map a`. -/
theorem relocalizeRepresentedIsoOfIso_comp {A U : BigFppfOver B W hW} {A' : BigFppfOver B S hS}
    (α : (Over.map h).obj A ≅ A') (a : A ⟶ U) (a' : A' ⟶ (Over.map h).obj U)
    (ha : α.hom ≫ a' = (Over.map h).map a) :
    relocalizeSpaceMap h (ObjectProperty.homMk (yoneda.map a) :
        representedAlgebraicSpace B W hW A ⟶ representedAlgebraicSpace B W hW U) ≫
        (relocalizeRepresentedIso h U).hom =
      (relocalizeRepresentedIsoOfIso h α).hom ≫ ObjectProperty.homMk (yoneda.map a') := by
  rw [relocalizeRepresentedIso_naturality, relocalizeRepresentedIsoOfIso, Iso.trans_hom,
    Category.assoc]
  congr 1
  ext1
  change yoneda.map ((Over.map h).map a) = yoneda.map α.hom ≫ yoneda.map a'
  rw [← Functor.map_comp, ha]

/-- The relocalization of the residue-field object of a point is the residue-field object of the
point in the relocalized object. -/
def residueFieldObjectRelocalizeIso (U : BigFppfOver B W hW) (x : U.left.1) :
    (Over.map h).obj
        (residueFieldObject B W hW U x (B.residueField_spec_contains U.left.property x)) ≅
      residueFieldObject B S hS ((Over.map h).obj U) x
        (B.residueField_spec_contains ((Over.map h).obj U).left.property x) :=
  Over.isoMk (Iso.refl _) (by
    apply ObjectProperty.hom_ext
    change 𝟙 _ ≫ U.left.1.fromSpecResidueField x ≫ (U.hom ≫ h).1 =
      (U.left.1.fromSpecResidueField x ≫ U.hom.1) ≫ h.1
    rw [Category.id_comp, Category.assoc]
    rfl)

/-- `residueFieldObjectRelocalizeIso` is compatible with the morphisms from the residue-field
objects to `(Over.map h).obj U`. -/
theorem residueFieldObjectRelocalizeIso_hom_comp (U : BigFppfOver B W hW) (x : U.left.1) :
    (residueFieldObjectRelocalizeIso h U x).hom ≫
        residueFieldMap B S hS ((Over.map h).obj U) x
          (B.residueField_spec_contains ((Over.map h).obj U).left.property x) =
      (Over.map h).map (residueFieldMap B W hW U x
        (B.residueField_spec_contains U.left.property x)) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact Category.id_comp _

include h in
/-- **Claim (A) of Stacks 0D3D over `S` gives it over `W`.** -/
theorem ampleSpreadsFromResidueFieldsToOpens_of_relocalize
    (hcore : AmpleSpreadsFromResidueFieldsToOpens B S hS) :
    AmpleSpreadsFromResidueFieldsToOpens B W hW := by
  intro U hU X' f' hf' L' hL' u hres
  let ιU := relocalizeRepresentedIso h U
  let fS : relocalizeSpace B hW hS h X' ⟶ representedAlgebraicSpace B S hS ((Over.map h).obj U) :=
    relocalizeSpaceMap h f' ≫ ιU.hom
  have hfS : IsProper B S hS fS.hom := by
    have : IsIso ιU.hom.hom := inferInstanceAs
      (IsIso (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U).hom)
    exact (isProper_comp_isIso_iff B S hS _ ιU.hom.hom).2
      ((isProper_relocalize_iff B W hW S hS h X'.2 (isAlgebraicSpace_yoneda B W hW U) f'.hom).2 hf')
  let E := moduleRelocalizeEquivalence B W S hW hS h X'
  let LS := E.inverse.obj L'
  have hLS : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (relocalizeSpace B hW hS h X').1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (relocalizeSpace B hW hS h X').1 (relocalizeSpace B hW hS h X').2).O)).property LS :=
    (isInvertible_moduleDerelocalize_iff h X' LS).1
      (isInvertible_of_iso_modules (E.counitIso.app L').symm hL')
  -- reading a pullback of `L'` over `S`
  have hread : ∀ {X₀ : AlgebraicSpaces B W hW} (p₀ : X₀ ⟶ X'),
      yoneda.relativelyRepresentable p₀.hom →
      ((moduleDerelocalize B W S hW hS h X₀).obj
          ((modulePullback B S hS (relocalizeSpaceMap h p₀)).obj LS) ≅
        (modulePullback B W hW p₀).obj L') := fun p₀ hp₀ =>
    ((modulePullbackRelocalizeIso h p₀ hp₀).app LS).symm ≪≫
      (modulePullback B W hW p₀).mapIso (E.counitIso.app L')
  have hinvread : ∀ {X₀ : AlgebraicSpaces B W hW} (p₀ : X₀ ⟶ X'),
      Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS (relocalizeSpace B hW hS h X₀).1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (relocalizeSpace B hW hS h X₀).1 (relocalizeSpace B hW hS h X₀).2).O)).property
        ((modulePullback B S hS (relocalizeSpaceMap h p₀)).obj LS) := fun p₀ =>
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS (relocalizeSpaceMap h p₀)) (L := LS) (hL := hLS)
  -- a base change of `f'` along a morphism of represented spaces is relatively representable
  have hrep : ∀ {X₀ A} {p₀ : X₀ ⟶ X'} {q : X₀ ⟶ representedAlgebraicSpace B W hW A} {a : A ⟶ U},
      IsPullback p₀ q f' (ObjectProperty.homMk (yoneda.map a)) →
        yoneda.relativelyRepresentable p₀.hom := fun {_ _ _ _ a} hsq =>
    MorphismProperty.of_isPullback (P := yoneda.relativelyRepresentable)
      (AlgebraicSpaces.isPullback_hom B W hW hsq).flip
      (Functor.relativelyRepresentable.map yoneda a)
  -- the hypothesis at the residue field, over `S`
  have hresS : ∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ relocalizeSpace B hW hS h X')
      (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS (residueFieldObject B S hS ((Over.map h).obj U) u
        (B.residueField_spec_contains ((Over.map h).obj U).left.property u))),
      IsPullback p₀ f₀ fS (ObjectProperty.homMk (yoneda.map (residueFieldMap B S hS
        ((Over.map h).obj U) u
          (B.residueField_spec_contains ((Over.map h).obj U).left.property u)))) →
      IsRelativelyAmple B S hS f₀ ((modulePullback B S hS p₀).obj LS) := by
    intro X₀' p₀' f₀' hsq'
    let gW : representedAlgebraicSpace B W hW
        (residueFieldObject B W hW U u (B.residueField_spec_contains U.left.property u)) ⟶
        representedAlgebraicSpace B W hW U :=
      ObjectProperty.homMk (yoneda.map (residueFieldMap B W hW U u
        (B.residueField_spec_contains U.left.property u)))
    have hsqW := AlgebraicSpaces.isPullback_fiberProduct B W hW f' gW
    have hampW := hres _ _ hsqW
    have hampΛ := (isRelativelyAmple_moduleDerelocalize_iff h _ _ (hinvread _)).1
      ((isRelativelyAmple_congr _ (hread _ (hrep hsqW))).2 hampW)
    let j := relocalizeRepresentedIsoOfIso h (residueFieldObjectRelocalizeIso h U u)
    have hc := relocalizeRepresentedIsoOfIso_comp h (residueFieldObjectRelocalizeIso h U u) _ _
      (residueFieldObjectRelocalizeIso_hom_comp h U u)
    have hsq₁ : IsPullback
        (relocalizeSpaceMap h (ObjectProperty.homMk (pullback.fst f'.hom gW.hom)))
        (relocalizeSpaceMap h (ObjectProperty.homMk (pullback.snd f'.hom gW.hom))) fS
        (j.hom ≫ ObjectProperty.homMk (yoneda.map (residueFieldMap B S hS ((Over.map h).obj U) u
          (B.residueField_spec_contains ((Over.map h).obj U).left.property u)))) :=
      (isPullback_relocalizeSpaceMap h hsqW).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ιU
        (by simp) (by simp) (by simp [fS]) (by simpa using hc)
    exact isRelativelyAmple_of_isPullback_of_isIso j hsq₁ hampΛ hsq'
  -- the open neighbourhood over `S`, read over `W`
  obtain ⟨V, huV, hV⟩ := hcore ((Over.map h).obj U) hU fS hfS LS hLS u hresS
  refine ⟨V, huV, fun X₁ p₁ f₁ hsq₁ => ?_⟩
  let gW : representedAlgebraicSpace B W hW (openSub U V) ⟶ representedAlgebraicSpace B W hW U :=
    ObjectProperty.homMk (yoneda.map (openSubHom U V))
  let j := relocalizeRepresentedIsoOfIso h (openSubRelocalizeIso h U V)
  have hc : relocalizeSpaceMap h gW ≫ ιU.hom =
      j.hom ≫ ObjectProperty.homMk (yoneda.map (openSubHom ((Over.map h).obj U) V)) :=
    relocalizeRepresentedIsoOfIso_comp h (openSubRelocalizeIso h U V) _ _
      (openSubRelocalizeIso_hom_comp h U V)
  have hsqB : IsPullback (relocalizeSpaceMap h p₁) (relocalizeSpaceMap h f₁) fS
      (relocalizeSpaceMap h gW ≫ ιU.hom) :=
    (isPullback_relocalizeSpaceMap h hsq₁).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ιU
      (by simp) (by simp) (by simp [fS]) (by simp [gW])
  have hsqA : IsPullback (relocalizeSpaceMap h p₁) (relocalizeSpaceMap h f₁ ≫ j.hom) fS
      (j.symm.hom ≫ (relocalizeSpaceMap h gW ≫ ιU.hom)) :=
    (isPullback_relocalizeSpaceMap h hsq₁).of_iso (Iso.refl _) (Iso.refl _) j ιU
      (by simp) (by simp) (by simp [fS]) (by simp [gW])
  have hampS := hV _ _ (by simpa [hc] using hsqA)
  have hampΛ := isRelativelyAmple_of_isPullback_of_isIso j.symm hsqA hampS hsqB
  have hampW := (isRelativelyAmple_moduleDerelocalize_iff h f₁ _ (hinvread p₁)).2 hampΛ
  exact (isRelativelyAmple_congr _ (hread p₁ (hrep hsq₁))).1 hampW

/-- **The open subspace of Stacks 0D3D, from claim (A) over the integers.** Let `f : X ⟶ Y` be a
proper morphism of algebraic spaces over `S` and `L` an invertible `𝒪_X`-module. Granted the fpqc
case of Stacks 0D3C over `S` and the residue-field form of claim (A) for algebraic spaces over
the terminal scheme `Spec ℤ`, there is an open subspace `V ⊆ Y` such that a morphism
`g : Y' ⟶ Y` factors through `V` if and only if the pullback of `L` to the base change of `f`
along `g` is ample. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleSpreadsOverIntegers
    (hZ : B.Contains (⊤_ Scheme.{u})) (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hcore : AmpleSpreadsFromResidueFieldsToOpens B (⊤_ Scheme.{u}) hZ)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) :=
  exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleSpreadsFromResidueFields hdesc
    (ampleSpreadsFromResidueFields_of_toOpens
      (ampleSpreadsFromResidueFieldsToOpens_of_relocalize
        (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) hcore)) hf hL

end AlgebraicGeometry.Space

end
