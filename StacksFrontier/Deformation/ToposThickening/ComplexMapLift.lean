module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.QuasiIsoOfAcyclicKernel
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.Homology.QuasiIsoKernel

/-!
# Lifting a map of complexes across a surjection of sheaves of rings

Let `f : O ⟶ O₀` be an epimorphism of sheaves of commutative rings on a site, `F` a complex of
`O`-modules, and `q : K₀ ⟶ O₀ ⊗_O F` a quasi-isomorphism of complexes of `O₀`-modules. Then `F`
can be replaced by a quasi-isomorphic complex `G` of `O`-modules for which the extension of
scalars of `G ⟶ F` factors through `q` in the homotopy category.

The proof is the one in the source: factor `q` as a homotopy equivalence followed by a
degreewise split epimorphism `L ⟶ O₀ ⊗_O F`, and let `G` be the pullback of the unit
`F ⟶ (O₀ ⊗_O F)|_O` along the restriction of that split epimorphism. Restriction of scalars
along an epimorphism of sheaves of rings preserves homology, so the pullback projection
`G ⟶ F` is a quasi-isomorphism, and the adjunction counit turns the second projection into the
required factorization.

## Main definitions

* `Deformation.ComplexLift.extensionOfScalarsCochainComplex`: extension of scalars along a
  morphism of sheaves of commutative rings, applied degreewise to cochain complexes of sheaves
  of modules.

## Main results

* `Deformation.ComplexLift.exists_quasiIso_with_extensionOfScalars_factorization`: the
  quasi-isomorphic replacement and its homotopy-category factorization.
* `Deformation.ComplexLift.exists_quasiIso_with_extensionOfScalars_factorization_of_hom`: the
  same for an arbitrary morphism of sheaves of rings, not necessarily an epimorphism.

## Implementation notes

The source's tensor product of a complex with the target sheaf of rings is the degreewise
extension-of-scalars functor `Stacks.Sheaves.RingedToposModules.extendScalars` of Stacks 03CZ.
The factorization is stated after applying `HomotopyCategory.quotient`, so the intervening
arrow is a genuine morphism in the homotopy category rather than a chosen chain map.

## References

* [Stacks Project, Tag 0DIX](https://stacks.math.columbia.edu/tag/0DIX)
-/

@[expose] public section

universe v' u u'

open CategoryTheory CategoryTheory.Functor Limits
open Stacks.Sheaves.RingedToposModules (extendScalars extendRestrictScalarsAdjunction
  commRingSheafMap)

namespace Deformation.ComplexLift

section Substrate

variable {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The morphism of underlying sheaves of rings induced by a morphism of sheaves of commutative
rings, in the same form. -/
abbrev ringSheafMapOf {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (O)) ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf (O₀)) :=
  Stacks.Sheaves.RingedToposModules.commRingSheafMap J f.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property

end Substrate

private theorem preservesColim_comp_transfer
    {A B D : Type*} [Category A] [Category B] [Category D]
    {K : Type*} [Category K] (E : K ⥤ A) (G : A ⥤ B) (F : B ⥤ D)
    (hG : PreservesColimit E G) (hGF : PreservesColimit E (G ⋙ F))
    [HasColimit E] : PreservesColimit (E ⋙ G) F :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves G (colimit.isColimit E))
    (isColimitOfPreserves (G ⋙ F) (colimit.isColimit E))

private theorem sheafOfModules_toSheaf_preservesFiniteColimits
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := by
  refine ⟨fun K _ _ => ?_⟩
  let Lsh : PresheafOfModules.{u} R.obj ⥤ SheafOfModules.{u} R :=
    PresheafOfModules.sheafification (𝟙 R.obj)
  let Gsh : SheafOfModules.{u} R ⥤ PresheafOfModules.{u} R.obj :=
    SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have hLsh : PreservesColimitsOfShape K Lsh := by
    let : PreservesColimitsOfSize.{0, 0} Lsh :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits
    infer_instance
  let : PreservesFiniteColimits (PresheafOfModules.toPresheaf R.obj) := inferInstance
  have : PreservesColimitsOfShape K (PresheafOfModules.toPresheaf R.obj) := by
    exact PreservesFiniteColimits.preservesFiniteColimits K
  have : PreservesColimitsOfShape K
      (presheafToSheaf J AddCommGrpCat.{u}) :=
    by
      let : PreservesColimitsOfSize.{0, 0} (presheafToSheaf J AddCommGrpCat.{u}) :=
        (sheafificationAdjunction J AddCommGrpCat.{u}).leftAdjoint_preservesColimits
      infer_instance
  have hcomp : PreservesColimitsOfShape K
      (Lsh ⋙ SheafOfModules.toSheaf.{u} R) := by
    have hiso : Lsh ⋙ SheafOfModules.toSheaf.{u} R ≅
        PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{u} :=
      PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)
    let : PreservesColimitsOfShape K
        (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{u}) :=
      comp_preservesColimitsOfShape _ _
    exact preservesColimitsOfShape_of_natIso hiso.symm
  let : Gsh ⋙ Lsh ≅ 𝟭 (SheafOfModules.{u} R) :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit
  refine ⟨fun {D} => ?_⟩
  have hkey : PreservesColimit ((D ⋙ Gsh) ⋙ Lsh)
      (SheafOfModules.toSheaf.{u} R) :=
    preservesColim_comp_transfer (D ⋙ Gsh) Lsh (SheafOfModules.toSheaf.{u} R)
      hLsh.preservesColimit hcomp.preservesColimit
  have hdiso : (D ⋙ Gsh) ⋙ Lsh ≅ D :=
    (Functor.associator D Gsh Lsh) ≪≫
      Functor.isoWhiskerLeft D (asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 R.obj)).counit) ≪≫ D.rightUnitor
  exact preservesColimit_of_iso_diagram (SheafOfModules.toSheaf.{u} R) hdiso

private def mapHomologicalComplexCompIso' {A B D : Type*}
    [Category A] [Category B] [Category D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]
    (F : A ⥤ B) (G : B ⥤ D) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (c : ComplexShape ℤ) :
  F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      (F ⋙ G).mapHomologicalComplex c :=
  NatIso.ofComponents
    (fun K => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
      (by intros; simp [Functor.comp_map])) (by
    intro K L f
    ext n
    simp [Functor.comp_map])

variable {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)

/-- Extension of scalars along `f`, applied degreewise to cochain complexes of
sheaves of modules. -/
noncomputable def extensionOfScalarsCochainComplex
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ℤ ⥤
      CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ℤ := by
  letI := (extendRestrictScalarsAdjunction J f.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property).isLeftAdjoint
  exact (extendScalars J f.hom (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The proof of the factorization theorems, which never uses that `f` is an epimorphism. -/
private theorem exists_quasiIso_factorization_aux
    {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
    {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ℤ)
    (K₀ : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ℤ)
    (q : K₀ ⟶ (extensionOfScalarsCochainComplex J f).obj F)
    (hq : QuasiIso q) :
    ∃ (G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ℤ)
      (g : G ⟶ F),
      QuasiIso g ∧
    (∃ h :
          (HomotopyCategory.quotient
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
              (ComplexShape.up ℤ)).obj
                ((extensionOfScalarsCochainComplex J f).obj G) ⟶
            (HomotopyCategory.quotient
                (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
              (ComplexShape.up ℤ)).obj K₀,
          (HomotopyCategory.quotient
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
                (ComplexShape.up ℤ)).map
              ((extensionOfScalarsCochainComplex J f).map g) =
            h ≫
              (HomotopyCategory.quotient
                  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
                (ComplexShape.up ℤ)).map q) := by
  let A := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))
  let B := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))
  let T : A ⥤ B := extendScalars J f.hom (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property
  let S : B ⥤ A := SheafOfModules.restrictScalars.{u}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (R' := Stacks.SheafOfModules.Tensor.ringSheaf O₀) (ringSheafMapOf J f)
  let adj : T ⊣ S := extendRestrictScalarsAdjunction J f.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property
  let : T.IsLeftAdjoint := adj.isLeftAdjoint
  let : S.Additive := SheafOfModules.instAdditiveRestrictScalars
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (R' := Stacks.SheafOfModules.Tensor.ringSheaf O₀) (ringSheafMapOf J f)
  let Tcomplex := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let Scomplex := S.mapHomologicalComplex (ComplexShape.up ℤ)
  let η :=
    (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).inv ≫
      NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ) ≫
      (mapHomologicalComplexCompIso' T S (ComplexShape.up ℤ)).inv
  let ε :=
      (mapHomologicalComplexCompIso' S T (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ) ≫
      (Functor.mapHomologicalComplexIdIso B (ComplexShape.up ℤ)).hom
  let Q := HomotopyCategory.quotient B (ComplexShape.up ℤ)
  obtain ⟨L, i, l, s, hil, hl, his, hh, _⟩ :=
    CochainComplex.exists_isDegreewiseSplitEpi_factorization q
  have hI : HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ) i := by
    change ∃ e : HomotopyEquiv K₀ L, e.hom = i
    exact ⟨⟨i, s, Homotopy.ofEq his, Classical.choice hh⟩, rfl⟩
  let : QuasiIso i := (homotopyEquivalences_le_quasiIso B (ComplexShape.up ℤ) i) hI
  have hlq : QuasiIso l := (quasiIso_iff_comp_left i l).1 (by simpa [hil] using hq)
  let F₀ := Tcomplex.obj F
  let l₀ : L ⟶ F₀ := l
  let G := pullback (η.app F) (Scomplex.map l₀)
  let g : G ⟶ F := pullback.fst (η.app F) (Scomplex.map l₀)
  let p : G ⟶ Scomplex.obj L := pullback.snd (η.app F) (Scomplex.map l₀)
  have hpull : g ≫ η.app F = p ≫ Scomplex.map l₀ := pullback.condition
  have hg : QuasiIso g := by
    have hlim : PreservesFiniteLimits S := by
      let : PreservesFiniteLimits
          (S ⋙ SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) := by
        change PreservesFiniteLimits
          (SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
        infer_instance
      exact preservesFiniteLimits_of_reflects_of_preserves S
        (SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))
    let : PreservesFiniteLimits S := hlim
    let U := SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))
    let V := SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))
    let : PreservesFiniteColimits U :=
      sheafOfModules_toSheaf_preservesFiniteColimits ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))
    let : PreservesFiniteColimits V :=
      sheafOfModules_toSheaf_preservesFiniteColimits ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))
    have hreflect : U.ReflectsEpimorphisms := by
      constructor
      intro X Y morphism hm
      have hmapCoker : cokernel.π (U.map morphism) = 0 := by
        apply (cancel_epi (U.map morphism)).1
        simp
      have hπ' : U.map (cokernel.π morphism) ≫
          (PreservesCokernel.iso U morphism).hom = 0 :=
        (PreservesCokernel.π_iso_hom U morphism).trans hmapCoker
      have hπ : U.map (cokernel.π morphism) = 0 :=
        (cancel_mono (PreservesCokernel.iso U morphism).hom).1 (by
          simpa using hπ')
      exact Abelian.epi_of_cokernel_π_eq_zero morphism (U.map_injective hπ)
    let : U.ReflectsEpimorphisms := hreflect
    have hcomp : S ⋙ U = V := rfl
    let : (S ⋙ U).PreservesEpimorphisms := by
      rw [hcomp]
      infer_instance
    let : S.PreservesEpimorphisms :=
      preservesEpimorphisms_of_preserves_of_reflects S U
    let : S.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels S
    let : QuasiIso l₀ := hlq
    let : QuasiIso (Scomplex.map l₀) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology l₀ S
    let : Epi (Scomplex.map l₀) := by
      apply HomologicalComplex.epi_of_epi_f
      intro n
      let : IsSplitEpi (l₀.f n) := hl n
      change Epi (S.map (l₀.f n))
      exact ((hl n).exists_splitEpi.some.map S).epi
    exact Stacks.KernelQuasiIso.pullback_fst_quasiIso_of_epi (η.app F) (Scomplex.map l₀)
  let : IsIso (Q.map i) :=
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences i).2 hI
  let a : Tcomplex.obj G ⟶ L := Tcomplex.map p ≫ ε.app L
  have htriangle : Tcomplex.map (η.app F) ≫ ε.app F₀ = 𝟙 (Tcomplex.obj F) := by
    apply HomologicalComplex.Hom.ext
    funext n
    change T.map ((η.app F).f n) ≫ (ε.app F₀).f n = 𝟙 _
    simp only [η, ε, mapHomologicalComplexCompIso', NatTrans.comp_app, id_obj, comp_obj,
      NatIso.ofComponents_inv_app, HomologicalComplex.comp_f, mapHomologicalComplex_obj_X,
      mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.refl_inv, Category.comp_id,
      Category.id_comp, NatIso.ofComponents_hom_app, HomologicalComplex.Hom.isoOfComponents_hom_f,
      Iso.refl_hom, mapHomologicalComplexIdIso_hom_app_f]
    exact adj.left_triangle_components (F.X n)
  have hεnat : ε.app L ≫ l₀ = Tcomplex.map (Scomplex.map l₀) ≫ ε.app F₀ := (ε.naturality l₀).symm
  have hal₀ : a ≫ l₀ = Tcomplex.map g := by
    dsimp [a]
    rw [Category.assoc, hεnat, ← Category.assoc, ← Functor.map_comp, ← hpull,
      Functor.map_comp, Category.assoc, htriangle, Category.comp_id]
  have hil₀ : i ≫ l₀ = q := hil
  refine ⟨G, g, hg, Q.map a ≫ inv (Q.map i), ?_⟩
  change K₀ ⟶ Tcomplex.obj F at q
  change Q.map (Tcomplex.map g) = (Q.map a ≫ inv (Q.map i)) ≫ Q.map q
  rw [← hal₀, Functor.map_comp, ← hil₀, Functor.map_comp]
  simp [Category.assoc]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A quasi-isomorphism to the extension of scalars of `F` can be lifted, after
replacing `F` by a quasi-isomorphic complex, to a factorization in the
homotopy category. -/
@[stacks 0DIX]
theorem exists_quasiIso_with_extensionOfScalars_factorization
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [Epi f]
    (F : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ℤ)
    (K₀ : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ℤ)
    (q : K₀ ⟶ (extensionOfScalarsCochainComplex J f).obj F)
    (hq : QuasiIso q) :
    ∃ (G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ℤ)
      (g : G ⟶ F),
      QuasiIso g ∧
    (∃ h :
          (HomotopyCategory.quotient
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
              (ComplexShape.up ℤ)).obj
                ((extensionOfScalarsCochainComplex J f).obj G) ⟶
            (HomotopyCategory.quotient
                (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
              (ComplexShape.up ℤ)).obj K₀,
          (HomotopyCategory.quotient
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
                (ComplexShape.up ℤ)).map
              ((extensionOfScalarsCochainComplex J f).map g) =
            h ≫
              (HomotopyCategory.quotient
                  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
                (ComplexShape.up ℤ)).map q) := by
  exact exists_quasiIso_factorization_aux J f F K₀ q hq

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A quasi-isomorphism to the extension of scalars of `F` can be lifted, after
replacing `F` by a quasi-isomorphic complex, to a factorization in the
homotopy category, for an arbitrary morphism `f` of sheaves of rings: the proof of
`Deformation.ComplexLift.exists_quasiIso_with_extensionOfScalars_factorization` never uses that
`f` is an epimorphism, since restriction of scalars is exact along any morphism. -/
theorem exists_quasiIso_with_extensionOfScalars_factorization_of_hom
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ℤ)
    (K₀ : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ℤ)
    (q : K₀ ⟶ (extensionOfScalarsCochainComplex J f).obj F)
    (hq : QuasiIso q) :
    ∃ (G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ℤ)
      (g : G ⟶ F),
      QuasiIso g ∧
    (∃ h :
          (HomotopyCategory.quotient
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
              (ComplexShape.up ℤ)).obj
                ((extensionOfScalarsCochainComplex J f).obj G) ⟶
            (HomotopyCategory.quotient
                (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
              (ComplexShape.up ℤ)).obj K₀,
          (HomotopyCategory.quotient
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
                (ComplexShape.up ℤ)).map
              ((extensionOfScalarsCochainComplex J f).map g) =
            h ≫
              (HomotopyCategory.quotient
                  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
                (ComplexShape.up ℤ)).map q) := by
  exact exists_quasiIso_factorization_aux J f F K₀ q hq

end Deformation.ComplexLift

end
