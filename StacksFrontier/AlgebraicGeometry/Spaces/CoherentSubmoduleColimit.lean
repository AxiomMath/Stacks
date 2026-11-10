module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces

/-!
# Coherent submodules of a quasi-coherent module on a locally Noetherian algebraic space

Let `X` be a locally Noetherian algebraic space over a scheme `S` and `F` a quasi-coherent
`𝒪_X`-module.  The coherent submodules of `F` form a directed system, and if `F` is a filtered
colimit of coherent modules, then `F` is the colimit of its coherent submodules.

## Main definitions

* `AlgebraicGeometry.Space.coherentSubobjectProperty` is the property of a subobject of `F`
  that its underlying module is coherent.
* `AlgebraicGeometry.Space.CoherentSubobject` is the category of coherent submodules of `F`,
  `AlgebraicGeometry.Space.coherentSubobjectFunctor` the diagram they form and
  `AlgebraicGeometry.Space.coherentSubobjectCocone` its canonical cocone with point `F`.

## Main results

* `AlgebraicGeometry.Space.isFiltered_coherentSubobject`: the coherent submodules of a
  quasi-coherent module on a locally Noetherian algebraic space form a directed system.
* `AlgebraicGeometry.Space.nonempty_isColimit_coherentSubobjectCocone`: given a filtered diagram
  of coherent modules with colimit `F`, the canonical cocone of the coherent submodules of `F` is a
  colimit cocone.

## References

* [Stacks Project, Tag 07UV](https://stacks.math.columbia.edu/tag/07UV)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The property of a subobject of `F` that its underlying module is coherent. -/
def coherentSubobjectProperty (F : Modules.{u, u} B S hS X hX) :
    ObjectProperty (Subobject F) :=
  fun G => IsCoherent B S hS X hX (G : Modules.{u, u} B S hS X hX)

/-- The category of coherent submodules of `F`, with the inclusions as morphisms. -/
abbrev CoherentSubobject (F : Modules.{u, u} B S hS X hX) :=
  (coherentSubobjectProperty B S hS X hX F).FullSubcategory

/-- The diagram of all coherent submodules of `F`. -/
noncomputable def coherentSubobjectFunctor (F : Modules.{u, u} B S hS X hX) :
    CoherentSubobject B S hS X hX F ⥤ Modules.{u, u} B S hS X hX :=
  (coherentSubobjectProperty B S hS X hX F).ι ⋙ Subobject.underlying

/-- The canonical cocone given by the inclusions of the coherent submodules of `F`. -/
noncomputable def coherentSubobjectCocone (F : Modules.{u, u} B S hS X hX) :
    Cocone (coherentSubobjectFunctor B S hS X hX F) :=
  Cocone.mk F
    { app := fun G => G.obj.arrow
      naturality := fun {_ _} f => Subobject.underlying_arrow f.hom }

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for image subobjects in the category of modules on the space is deep
/-- On a locally Noetherian algebraic space, the image in a quasi-coherent module `F` of a
morphism from a coherent module is a coherent submodule of `F`. -/
theorem isCoherent_imageSubobject
    [Fact (HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {M F : Modules.{u, u} B S hS X hX} (f : M ⟶ F) (hM : IsCoherent B S hS X hX M)
    (hF : F.IsQuasicoherentOnSite) :
    IsCoherent B S hS X hX ((imageSubobject f : Subobject F) : Modules.{u, u} B S hS X hX) := by
  have hker := isClosedUnderKernels_quasicoherentSheaves B S hS X hX
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX)
  have hcoker := isClosedUnderCokernels_quasicoherentSheaves B S hS X hX
  have hq : ((imageSubobject f : Subobject F) :
      Modules.{u, u} B S hS X hX).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_image B S hS X hX hker hcoker f hM.toIsQuasicoherentOnSite hF
  have hepi : Epi (factorThruImageSubobject f) := by
    dsimp [factorThruImageSubobject]
    apply epi_comp
  exact isCoherent_of_epi_of_isQuasicoherentOnSite B S hS X hX
    (factorThruImageSubobject f) hq hM

/-- The coherent submodules of a quasi-coherent `𝒪_X`-module on a locally Noetherian algebraic
space form a directed system. -/
theorem isFiltered_coherentSubobject
    [Fact (HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite] :
    IsFiltered (CoherentSubobject B S hS X hX F) := by
  classical
  let P := coherentSubobjectProperty B S hS X hX F
  refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := ?_ }
  · intro A D
    have : HasBinaryBiproduct (A.1 : Modules.{u, u} B S hS X hX)
      (D.1 : Modules.{u, u} B S hS X hX) := inferInstance
    have hsum : IsCoherent B S hS X hX
        ((A.1 : Modules.{u, u} B S hS X hX) ⊞ (D.1 : Modules.{u, u} B S hS X hX)) :=
      (isCoherent.{u, u} B S hS X hX).prop_biprod A.2 D.2
    let f : (A.1 : Modules.{u, u} B S hS X hX) ⊞ (D.1 : Modules.{u, u} B S hS X hX) ⟶ F :=
      biprod.desc A.1.arrow D.1.arrow
    let I : Subobject F := imageSubobject f
    have hAle : A.1 ≤ I := by
      apply Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject f)
      change (biprod.inl ≫ factorThruImageSubobject f) ≫ I.arrow = A.1.arrow
      rw [Category.assoc, imageSubobject_arrow_comp]
      simp [f]
    have hDle : D.1 ≤ I := by
      apply Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject f)
      change (biprod.inr ≫ factorThruImageSubobject f) ≫ I.arrow = D.1.arrow
      rw [Category.assoc, imageSubobject_arrow_comp]
      simp [f]
    exact ⟨⟨I, isCoherent_imageSubobject B S hS X hX f hsum ‹_›⟩, P.homMk (homOfLE hAle),
      P.homMk (homOfLE hDle), trivial⟩
  · intro A D f g
    exact ⟨D, 𝟙 D, P.hom_ext (Subsingleton.elim _ _)⟩
  · have hz : IsZero ((⊥ : Subobject F) : Modules.{u, u} B S hS X hX) :=
      IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
    exact ⟨⟨⊥, IsCoherent.of_isZero B S hS X hX hz⟩⟩

/-- Given a filtered diagram of coherent `𝒪_X`-modules with colimit `F`, the canonical cocone of
the coherent submodules of `F` is a colimit cocone. -/
theorem nonempty_isColimit_coherentSubobjectCocone
    [Fact (HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (J : Type u) [instJ : SmallCategory J] [_instJ : IsFiltered J]
    (D : J ⥤ Modules.{u, u} B S hS X hX) (φ : D ⟶ (Functor.const J).obj F)
    (hD : ∀ j, IsCoherent B S hS X hX (D.obj j))
    (hcol : IsColimit (Cocone.mk F φ)) :
    Nonempty (IsColimit (coherentSubobjectCocone B S hS X hX F)) := by
  classical
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X hX).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X)
    infer_instance
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hfiltered : IsFiltered (CoherentSubobject B S hS X hX F) :=
    isFiltered_coherentSubobject B S hS X hX F
  have htop : (⨆ G : CoherentSubobject B S hS X hX F, G.obj) = (⊤ : Subobject F) := by
    refine le_antisymm le_top ?_
    rw [← iSup_imageSubobject_eq_top_of_isColimit φ hcol]
    refine iSup_le fun j => ?_
    exact le_iSup (fun G : CoherentSubobject B S hS X hX F => G.obj)
      ⟨imageSubobject (φ.app j),
        isCoherent_imageSubobject B S hS X hX (φ.app j) (hD j) ‹_›⟩
  exact ⟨isColimitSubobjectCocone_of_iSup_eq_top
    (coherentSubobjectProperty B S hS X hX F) htop⟩

end AlgebraicGeometry.Space

end
