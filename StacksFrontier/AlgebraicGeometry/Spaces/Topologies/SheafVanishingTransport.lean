module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transporting the vanishing of abelian sheaves and of their higher direct images

Higher right derived functors commute with exact functors in a commuting square, a commuting
square of right adjoints gives one of left adjoints, an abelian sheaf on a localized site
vanishes when its sections over a cover-dense image do, and abelian inverse images preserve
torsion sheaves.

## Main definitions

* `Stacks.Cohomology.rightDerivedObjIsoOfCommSquare`: if `F ⋙ T ≅ R ⋙ F'` with `R` exact and
  preserving injective objects and `T` exact, then `T (Rⁿ F M) ≅ Rⁿ F' (R M)`.
* `Stacks.Cohomology.leftAdjointCompIsoOfRightAdjointComp`: a commuting square of right
  adjoints whose two other sides are equivalences gives a commuting square of left adjoints.

## Main results

* `Stacks.Cohomology.isZero_sheafOver_of_isZero_sections_overImage`: an abelian sheaf on a
  localized site vanishes as soon as its sections over the objects coming from a cover-dense
  functor vanish.
* `Stacks.Torsion.torsionSheafProperty_abelianInverseImage`: the abelian inverse image of a
  morphism of topoi preserves torsion abelian sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology

section RightDerived

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasInjectiveResolutions A] [HasInjectiveResolutions A']

/-- **Higher right derived functors commute with exact functors in a commuting square.** If
`F ⋙ T ≅ R ⋙ F'`, where `R` is exact and preserves injective objects and `T` is exact, then
`T (Rⁿ F M) ≅ Rⁿ F' (R M)`. -/
def rightDerivedObjIsoOfCommSquare (F : A ⥤ B) (F' : A' ⥤ B') (R : A ⥤ A') (T : B ⥤ B')
    [F.Additive] [F'.Additive] [R.Additive] [T.Additive]
    [R.PreservesHomology] [PreservesFiniteLimits R] [R.PreservesInjectiveObjects]
    [T.PreservesHomology]
    (e : F ⋙ T ≅ R ⋙ F') (M : A) (n : ℕ) :
    T.obj ((F.rightDerived n).obj M) ≅ (F'.rightDerived n).obj (R.obj M) :=
  let I := injectiveResolution M
  let I' : InjectiveResolution (R.obj M) :=
    Stacks.RightDerivedComp.mapOfAcyclic R I
      (fun k hk ↦ isZero_rightDerived_obj_of_preservesHomology R M k hk)
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  T.mapIso (I.isoRightDerivedObj F n) ≪≫
    (ShortComplex.mapHomologyIso (K.sc n) T).symm ≪≫
    (HomologicalComplex.homologyFunctor B' (ComplexShape.up ℕ) n).mapIso
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).app I.cocomplex) ≪≫
    (I'.isoRightDerivedObj F' n).symm

/-- Under the hypotheses of `Stacks.Cohomology.rightDerivedObjIsoOfCommSquare`, if moreover `T`
is faithful, the vanishing of `Rⁿ F' (R M)` implies the vanishing of `Rⁿ F M`. -/
theorem isZero_rightDerived_obj_of_commSquare (F : A ⥤ B) (F' : A' ⥤ B') (R : A ⥤ A')
    (T : B ⥤ B') [F.Additive] [F'.Additive] [R.Additive] [T.Additive]
    [R.PreservesHomology] [PreservesFiniteLimits R] [R.PreservesInjectiveObjects]
    [T.PreservesHomology] [T.Faithful]
    (e : F ⋙ T ≅ R ⋙ F') (M : A) (n : ℕ)
    (h : IsZero ((F'.rightDerived n).obj (R.obj M))) :
    IsZero ((F.rightDerived n).obj M) := by
  have hT := (rightDerivedObjIsoOfCommSquare F F' R T e M n).isZero_iff.mpr h
  rw [IsZero.iff_id_eq_zero] at hT ⊢
  exact T.map_injective (by rw [T.map_id, T.map_zero, hT])

end RightDerived

/-- **A commuting square of right adjoints gives one of left adjoints.** Given adjunctions
`L ⊣ R` and `L' ⊣ R'` and equivalences `e` and `d` with `R ⋙ e.functor ≅ d.functor ⋙ R'`,
the left adjoints satisfy `L ⋙ d.functor ≅ e.functor ⋙ L'`. -/
def leftAdjointCompIsoOfRightAdjointComp
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (a : L ⊣ R) (b : L' ⊣ R') (e : A ≌ A') (d : B ≌ B')
    (α : R ⋙ e.functor ≅ d.functor ⋙ R') :
    L ⋙ d.functor ≅ e.functor ⋙ L' :=
  let β : d.inverse ⋙ R ≅ R' ⋙ e.inverse :=
    Functor.isoWhiskerLeft (d.inverse ⋙ R) e.unitIso ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft d.inverse α) e.inverse ≪≫
      Functor.isoWhiskerRight d.counitIso (R' ⋙ e.inverse)
  Adjunction.leftAdjointUniq ((a.comp d.toAdjunction).ofNatIsoRight β)
    (e.toAdjunction.comp b)

/-- **Vanishing on a cover-dense image.** Let `G : C ⥤ D` be cover-dense for a topology `J` on
`D`, and let `M` be an abelian sheaf on `D` localized at `X`. If the sections of `M` vanish over
every object `G V ⟶ X` coming from `C`, then `M` vanishes. -/
theorem isZero_sheafOver_of_isZero_sections_overImage
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    (J : GrothendieckTopology D) [G.IsCoverDense J] (X : D)
    {𝒜 : Type*} [Category* 𝒜] [HasZeroMorphisms 𝒜] (M : Sheaf (J.over X) 𝒜)
    (hM : ∀ (V : C) (f : G.obj V ⟶ X), IsZero (M.obj.obj (op (Over.mk f)))) : IsZero M := by
  refine Sheaf.isZero_of_isCoveringFamily M
    (P := fun W ↦ ∃ (V : C) (f : G.obj V ⟶ X), W = Over.mk f) (fun U ↦ ?_) ?_
  · refine ⟨Presieve.ofArrows (fun i : Σ V : C, G.obj V ⟶ U.left ↦ Over.mk (i.2 ≫ U.hom))
      (fun i ↦ Over.homMk i.2), ?_, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff]
      refine J.superset_covering ?_ (G.is_cover_of_isCoverDense J U.left)
      rintro Z g ⟨⟨V, a, b, hab⟩⟩
      rw [Sieve.overEquiv_iff]
      refine ⟨Over.mk (b ≫ U.hom), Over.homMk a (by simp [← hab]), Over.homMk b,
        Presieve.ofArrows.mk (⟨V, b⟩ : Σ V : C, G.obj V ⟶ U.left), ?_⟩
      ext
      simp [hab]
    · rintro W g ⟨i⟩
      exact ⟨i.1, i.2 ≫ U.hom, rfl⟩
  · rintro W ⟨V, f, rfl⟩
    exact hM V f

end Stacks.Cohomology

namespace Stacks.Torsion

universe w w'

/-- Equal morphisms of sheaves with values in a concrete category agree on sections. -/
private theorem sheaf_hom_app_apply_congr
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {D : Type*} [Category* D]
    {FD : D → D → Type*} {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] {F G : Sheaf J D} {a b : F ⟶ G} (h : a = b) (U : Cᵒᵖ)
    (x : ToType (F.obj.obj U)) : a.hom.app U x = b.hom.app U x := by
  subst h
  rfl

/-- A section of an abelian sheaf killed by a morphism lifts to the kernel. -/
private theorem exists_kernel_section_lift
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}]
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (U : Cᵒᵖ)
    (x : F.obj.obj U) (hx : f.hom.app U x = 0) :
    ∃ y : (kernel f).obj.obj U, (kernel.ι f).hom.app U y = x := by
  let ev := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  let e := PreservesKernel.iso ev f ≪≫ AddCommGrpCat.kernelIsoKer (ev.map f)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  have hh : e.inv ≫ ev.map (kernel.ι f) =
      AddCommGrpCat.ofHom (ev.map f).hom.ker.subtype := by
    simp only [e, Iso.trans_inv, Category.assoc, PreservesKernel.iso_inv_ι,
      AddCommGrpCat.kernelIsoKer_inv_comp_ι]
  exact ConcreteCategory.congr_hom hh ⟨x, hx⟩

/-- Two maps out of the underlying sheaf of sets of a torsion abelian sheaf agree as soon as
they agree on the underlying sheaves of sets of its `n`-torsion subsheaves for every `n > 0`. -/
private theorem torsionSheaf_forget_hom_ext
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}]
    (F : Sheaf J AddCommGrpCat.{w}) (hF : torsionSheafProperty J F)
    {G : Sheaf J (Type w)}
    (a b : (sheafCompose J (forget AddCommGrpCat.{w})).obj F ⟶ G)
    (h : ∀ (n : ℕ), 0 < n →
      (sheafCompose J (forget AddCommGrpCat.{w})).map (kernel.ι (n • 𝟙 F)) ≫ a =
      (sheafCompose J (forget AddCommGrpCat.{w})).map (kernel.ι (n • 𝟙 F)) ≫ b) : a = b := by
  ext U x
  obtain ⟨R, hR, hr⟩ := hF U.unop x
  apply ((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property R hR).isSeparatedFor.ext
  intro V g hg
  obtain ⟨n, hn, hnx⟩ := hr V g hg
  obtain ⟨y, hy⟩ := exists_kernel_section_lift (n • 𝟙 F) (op V) (F.obj.map g.op x)
    (by change n • F.obj.map g.op x = 0; exact hnx)
  have he := sheaf_hom_app_apply_congr (h n hn) (op V) y
  change a.hom.app (op V) ((kernel.ι (n • 𝟙 F)).hom.app (op V) y) =
    b.hom.app (op V) ((kernel.ι (n • 𝟙 F)).hom.app (op V) y) at he
  rw [hy] at he
  exact (a.hom.naturality_apply g.op x).symm.trans (he.trans (b.hom.naturality_apply g.op x))

/-- **The abelian inverse image of a morphism of topoi preserves torsion sheaves.** -/
@[sga "4 IX 1.2" "(iv)"]
theorem torsionSheafProperty_abelianInverseImage
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J (Type w)] [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w'}]
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (F : Sheaf K AddCommGrpCat.{w'}) (hF : torsionSheafProperty K F) :
    torsionSheafProperty J ((Sites.abelianInverseImage f).obj F) := by
  let L := Sites.abelianInverseImage f
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  let M := L.obj F
  let U := sheafCompose J (forget AddCommGrpCat.{w})
  let V := sheafCompose K (forget AddCommGrpCat.{w'})
  let A : Subfunctor (U.obj M).obj := {
    obj X := {x : M.obj.obj X | ∃ n : ℕ, 0 < n ∧ n • x = 0}
    map := by
      rintro X Y g x ⟨n, hn, hx⟩
      let x' : M.obj.obj X := x
      exact ⟨n, hn, (map_nsmul (M.obj.map g).hom n x').symm.trans
        ((congrArg (M.obj.map g).hom (show n • x' = 0 from hx)).trans (map_zero _))⟩ }
  let T : Sheaf J (Type w) := ⟨(A.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).mpr
      (A.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J _).mp (U.obj M).property))⟩
  let j : T ⟶ U.obj M := ⟨(A.sheafify J).ι⟩
  let e : U.obj M ≅ f.inverseImage.obj (V.obj F) := (Sites.abelianInverseImage_forgetIso f).app F
  have hm (n : ℕ) (hn : 0 < n) :
      ∃ l : f.inverseImage.obj (V.obj (kernel (n • 𝟙 F))) ⟶ T,
        l ≫ j ≫ e.hom = f.inverseImage.map (V.map (kernel.ι (n • 𝟙 F))) := by
    let k := L.map (kernel.ι (n • 𝟙 F))
    have hk : k ≫ (n • 𝟙 M) = 0 := by
      change L.map (kernel.ι (n • 𝟙 F)) ≫ (n • 𝟙 (L.obj F)) = 0
      rw [← L.map_id, ← L.map_nsmul, ← L.map_comp, kernel.condition, L.map_zero]
    have hk' (X : Cᵒᵖ) (x : (L.obj (kernel (n • 𝟙 F))).obj.obj X) :
        n • k.hom.app X x = 0 :=
      sheaf_hom_app_apply_congr hk X x
    let t := (f.inverseImage.map (V.map (kernel.ι (n • 𝟙 F)))).hom
    have ht : Subfunctor.range t ≤ A.sheafify J := by
      rintro X _ ⟨x, rfl⟩
      exact A.le_sheafify J _ ⟨n, hn, hk' X x⟩
    refine ⟨⟨Subfunctor.lift t ht⟩, ?_⟩
    rw [← Category.assoc]
    exact Sheaf.hom_ext (Subfunctor.lift_ι t ht)
  have : Epi j := ⟨by
    intro Z a b hab
    rw [← cancel_epi e.inv]
    apply (f.adj.homEquiv (V.obj F) Z).injective
    apply torsionSheaf_forget_hom_ext F hF
    intro n hn
    rw [← f.adj.homEquiv_naturality_left, ← f.adj.homEquiv_naturality_left]
    congr 1
    obtain ⟨l, hl⟩ := hm n hn
    rw [← hl, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, Category.assoc,
      Category.assoc, Iso.hom_inv_id_assoc, hab]⟩
  have : Mono j := (sheafToPresheaf J (Type w)).mono_of_mono_map
    (inferInstanceAs (Mono (A.sheafify J).ι))
  have : IsIso j := isIso_of_mono_of_epi j
  intro X x
  let y := (inv j).hom.app (op X) x
  have hy : j.hom.app (op X) y = x :=
    sheaf_hom_app_apply_congr (IsIso.inv_hom_id j) (op X) x
  exact ⟨A.sieveOfSection x, hy ▸ y.property, fun Y g hg ↦ hg⟩

end Stacks.Torsion
