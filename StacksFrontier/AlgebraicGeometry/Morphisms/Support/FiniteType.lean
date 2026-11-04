module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Support of a finite type module and its fibres

For a finite type quasi-coherent module on a scheme, its stalk at a point is nonzero if and
only if its fibre over the residue field at that point is nonzero.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nontrivial_stalk_iff_nontrivial_fibre` characterizes the
  nonvanishing of a stalk by the nonvanishing of its residue-field fibre.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

namespace SheafOfModules

open CategoryTheory Limits Opposite TopologicalSpace

universe u

section

universe v w

/-- The image of a section of a free sheaf of modules under the map classified by a finite
family of global sections lies in the span of that family. -/
lemma free_image_mem_span {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} {I : Type u} [Finite I] (s : I → M.sections)
    (U : Cᵒᵖ) (a : (SheafOfModules.free (R := R) I).val.obj U) :
    (M.freeHomEquiv.symm s).val.app U a ∈
      Submodule.span (M := M.val.obj U) (R.obj.obj U)
        (Set.range (fun i => ((s i).val U : M.val.obj U))) := by
  let S := Submodule.span (M := M.val.obj U) (R.obj.obj U)
    (Set.range (fun i => ((s i).val U : M.val.obj U)))
  let E := SheafOfModules.evaluation R U
  have : E.Additive := { map_add := by intros; rfl }
  let q : E.obj M ⟶ ModuleCat.of _ (_ ⧸ S) := ModuleCat.ofHom S.mkQ
  have hzero : E.map (M.freeHomEquiv.symm s) ≫ q = 0 := by
    apply (isColimitOfPreserves E (SheafOfModules.isColimitFreeCofan I)).hom_ext
    rintro ⟨i⟩
    show E.map (SheafOfModules.ιFree i) ≫ (E.map (M.freeHomEquiv.symm s) ≫ q) = _
    rw [← Category.assoc, ← E.map_comp]
    have hgen : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s =
        M.unitHomEquiv.symm (s i) := by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      exact congrArg M.unitHomEquiv.symm (congrFun (M.freeHomEquiv.apply_symm_apply s) i)
    rw [hgen]
    refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
    show S.mkQ (@SMul.smul (R.obj.obj U) (M.val.obj U) _ r ((s i).val U)) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr
      (S.smul_mem r (Submodule.subset_span ⟨i, rfl⟩))
  exact (Submodule.Quotient.mk_eq_zero S).mp (congrArg (fun f => f.hom a) hzero)

/-- An epimorphism of sheaves of modules is locally surjective on underlying abelian sheaves. -/
lemma isLocallySurjective_toSheaf_of_epi {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf R).map f).hom := by
  have : PreservesColimit (span f f) (SheafOfModules.toSheaf R) := by
    let L := PresheafOfModules.sheafification (R := R) (𝟙 R.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)
    let Rt := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
    let K : WalkingSpan ⥤ PresheafOfModules R.obj := span f f ⋙ Rt
    have : PreservesColimit K (L ⋙ SheafOfModules.toSheaf R) :=
      preservesColimit_of_natIso K
        (PresheafOfModules.sheafificationCompToSheaf (R := R) (𝟙 R.obj)).symm
    let e : span f f ≅ K ⋙ L :=
      (Functor.rightUnitor (span f f)).symm ≪≫
        Functor.isoWhiskerLeft (span f f) (asIso adj.counit).symm ≪≫
        (Functor.associator (span f f) Rt L).symm
    have : PreservesColimit (K ⋙ L) (SheafOfModules.toSheaf R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit K))
        (isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf R) (colimit.isColimit K))
    exact preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R) e.symm
  have := preserves_epi_of_preservesColimit (SheafOfModules.toSheaf R) f
  exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat
    ((SheafOfModules.toSheaf R).map f)).mpr inferInstance

/-- If a section of a presheaf of modules over an open set `W` lies in the span of a family of
sections over `W`, then its germ at a point of `W` lies in the span of the germs of that family
over the stalk of the structure presheaf. -/
lemma germ_mem_span_germ {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) {x : X} {W : Opens X}
    (hx : x ∈ W) {ι : Type*} (b : ι → M.obj (op W)) {y : M.obj (op W)}
    (hy : y ∈ Submodule.span ↑(R.obj (op W)) (Set.range b)) :
    TopCat.Presheaf.germ M.presheaf W x hx y ∈
      Submodule.span ↑(TopCat.Presheaf.stalk R x)
        (Set.range fun i => TopCat.Presheaf.germ M.presheaf W x hx (b i)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
      have h0 : TopCat.Presheaf.germ M.presheaf W x hx (0 : ↑(M.obj (op W))) = 0 := map_zero _
      rw [h0]
      exact Submodule.zero_mem _
  | add z w _ _ hz hw =>
      have hadd : TopCat.Presheaf.germ M.presheaf W x hx (z + w) =
          TopCat.Presheaf.germ M.presheaf W x hx z
            + TopCat.Presheaf.germ M.presheaf W x hx w := map_add _ _ _
      rw [hadd]
      exact Submodule.add_mem _ hz hw
  | smul r z _ hz =>
      rw [PresheafOfModules.germ_smul]
      exact Submodule.smul_mem _ _ hz

/-- The germs at `x` of a finite family of generating sections on a neighbourhood `V` of `x`
span the stalk at `x` over the stalk of the structure sheaf. -/
lemma span_germ_generators_eq_top {X : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} X)
    (F : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
    (x : X) (V : Opens X) (hxV : x ∈ V) (gs : (F.over V).GeneratingSections)
    [Finite gs.I] :
    letI : Module ↑(TopCat.Presheaf.stalk R.obj x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    Submodule.span ↑(TopCat.Presheaf.stalk R.obj x)
        (Set.range (fun j : gs.I => TopCat.Presheaf.germ F.val.presheaf V x hxV
          ((gs.s j).val (op (Over.mk (𝟙 V)))))) = ⊤ := by
  let : Module ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  let : Fintype gs.I := Fintype.ofFinite _
  let s (j : gs.I) : ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
    TopCat.Presheaf.germ F.val.presheaf V x hxV ((gs.s j).val (op (Over.mk (𝟙 V))))
  let S := Submodule.span ↑(TopCat.Presheaf.stalk R.obj x) (Set.range s)
  show S = ⊤
  refine top_unique fun m _ ↦ ?_
  obtain ⟨U, hUV, hxU, t, ht⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf m hxV
  have := isLocallySurjective_toSheaf_of_epi gs.π
  have hmem := Presheaf.imageSieve_mem ((Opens.grothendieckTopology X).over V)
    ((SheafOfModules.toSheaf _).map gs.π).hom (U := op (Over.mk (homOfLE hUV))) t
  rw [GrothendieckTopology.mem_over_iff] at hmem
  obtain ⟨W, f, ⟨Z, g, h, ⟨a, ha⟩, _⟩, hxW⟩ := hmem x hxU
  have hWU : W ≤ U := leOfHom f
  let Wo : Over V := Over.mk (homOfLE (le_trans hWU hUV))
  let k : Wo ⟶ Z := Over.homMk h (Subsingleton.elim _ _)
  let a' := (SheafOfModules.free (R := ((sheafCompose _
    (forget₂ CommRingCat RingCat.{u})).obj R).over V) gs.I).val.presheaf.map k.op a
  have key : gs.π.val.app (op Wo) a' = F.val.presheaf.map f.op t := by
    have ha' : gs.π.val.app (op Z) a = (F.over V).val.map g.op t := ha
    have hslice := PresheafOfModules.naturality_apply gs.π.val k.op a
    rwa [ha', ← (F.over V).val.map_comp_apply g.op k.op t] at hslice
  have hspan := free_image_mem_span gs.s (op Wo) a'
  rw [key] at hspan
  have hm : TopCat.Presheaf.germ F.val.presheaf W x hxW (F.val.presheaf.map f.op t) = m := by
    rwa [TopCat.Presheaf.germ_res_apply]
  have hjg : ∀ j : gs.I,
      TopCat.Presheaf.germ F.val.presheaf W x hxW ((gs.s j).val (op Wo)) = s j := fun j ↦ by
    have hj := PresheafOfModules.sections_property (gs.s j)
      (Over.homMk (homOfLE (le_trans hWU hUV)) : Wo ⟶ Over.mk (𝟙 V)).op
    rw [← hj]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [← hm]
  refine Submodule.span_le.mpr ?_
    (germ_mem_span_germ F.val hxW (fun j => (gs.s j).val (op Wo)) hspan)
  rintro y ⟨j, rfl⟩
  exact Submodule.subset_span ⟨j, (hjg j).symm⟩

/-- The stalk of a finite type sheaf of modules is a finite module over the stalk of the
structure sheaf. -/
lemma finite_stalk {X : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} X)
    (F : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) [F.IsFiniteType]
    (x : X) :
    letI : Module ↑(TopCat.Presheaf.stalk R.obj x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    Module.Finite ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x) := by
  let : Module ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨U₀, _, ⟨i, ⟨g₀⟩⟩, hxU₀⟩ := σ.coversTop ⊤ x (by trivial)
  have hxV : x ∈ σ.X i := (leOfHom g₀) hxU₀
  have : Finite (σ.generators i).I := (hσ.isFiniteType i).finite
  exact ⟨(span_germ_generators_eq_top R F x (σ.X i) hxV (σ.generators i)) ▸
    Submodule.fg_span (Set.finite_range _)⟩

end

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Limits Opposite TopologicalSpace

universe u

/-- A finite type quasi-coherent module has nonzero stalk at `x` exactly when its fibre over
the residue field at `x` is nonzero. -/
@[stacks 056J "support_by_fibre"]
lemma nontrivial_stalk_iff_nontrivial_fibre
    {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        F.val x
    letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
      (X.residue x).hom.toAlgebra
    Nontrivial (F.presheaf.stalk x) ↔
      Nontrivial (TensorProduct (X.presheaf.stalk x)
        (F.presheaf.stalk x) (X.residueField x)) := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      F.val x
  let : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  rw [← not_subsingleton_iff_nontrivial, ← not_subsingleton_iff_nontrivial]
  exact not_congr ((TensorProduct.comm (X.presheaf.stalk x)
    (F.presheaf.stalk x) (X.residueField x)).toEquiv.subsingleton_congr.trans
      IsLocalRing.subsingleton_tensorProduct).symm

end AlgebraicGeometry.Scheme.Modules
