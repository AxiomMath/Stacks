module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Morphisms out of the restriction of an associated sheaf to an open

For an `R`-module `M`, an `𝒪_{Spec R}`-module `F` and an open `U ⊆ Spec R`, morphisms
`M̃|_U ⟶ F|_U` of modules on the slice site over `U` correspond to `R`-linear maps
`M ⟶ F(U)`, by evaluation at `U` on the canonical sections. Applied degreewise this identifies the
Hom complex from `Ã|_U` to `I|_U` with the Hom complex of `R`-modules from `A` to the sections of
`I` over `U`.

## Main definitions

* `AlgebraicGeometry.TildeSlice.tildeOverHomEquiv`: the correspondence for modules.
* `AlgebraicGeometry.TildeSlice.homComplexTildeOverIso`: the correspondence for Hom complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace CochainComplex.HomComplex

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
  {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}
  (e : ∀ p q : ℤ, (K.X p ⟶ L.X q) ≃+ (K'.X p ⟶ L'.X q))

/-- Cochains are transported along a family of additive equivalences of morphism groups. -/
def cochainAddEquiv (n : ℤ) : Cochain K L n ≃+ Cochain K' L' n where
  toFun z := Cochain.mk fun p q h => e p q (z.v p q h)
  invFun z := Cochain.mk fun p q h => (e p q).symm (z.v p q h)
  left_inv z := by ext p q h; simp
  right_inv z := by ext p q h; simp
  map_add' z z' := by ext p q h; simp

/-- The components of a transported cochain are the images of the components. -/
@[simp]
lemma cochainAddEquiv_v (n : ℤ) (z : Cochain K L n) (p q : ℤ) (h : p + n = q) :
    (cochainAddEquiv e n z).v p q h = e p q (z.v p q h) := by
  simp [cochainAddEquiv]

variable (comp_d : ∀ (p q q' : ℤ) (f : K.X p ⟶ L.X q), e p q' (f ≫ L.d q q') = e p q f ≫ L'.d q q')
  (d_comp : ∀ (p' p q : ℤ) (f : K.X p ⟶ L.X q), e p' q (K.d p' p ≫ f) = K'.d p' p ≫ e p q f)

include comp_d d_comp in
/-- Transport of cochains commutes with the differential when the equivalences are compatible with
the differentials. -/
lemma δ_cochainAddEquiv (n m : ℤ) (z : Cochain K L n) :
    δ n m (cochainAddEquiv e n z) = cochainAddEquiv e m (δ n m z) := by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    rw [δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl]
    simp only [cochainAddEquiv_v]
    rw [δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, map_add, comp_d, Units.smul_def,
      Units.smul_def, map_zsmul, d_comp]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, map_zero]

include comp_d d_comp in
/-- Hom complexes are isomorphic along a family of additive equivalences of morphism groups
compatible with the differentials. -/
def homComplexIsoOfAddEquiv : HomComplex K L ≅ HomComplex K' L' :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainAddEquiv e n).toAddCommGrpIso)
    (fun n m _ => by
      ext z
      exact δ_cochainAddEquiv e comp_d d_comp n m z)

end CochainComplex.HomComplex

namespace AlgebraicGeometry.TildeSlice

variable {R : CommRingCat.{u}} (U : (Spec R).Opens)

/-- Sections over `U` of an `𝒪_{Spec R}`-module, as an `R`-module. -/
abbrev sectionsR : (Spec R).Modules ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)

/-- Taking sections over `U` is an additive functor. -/
instance sectionsR_additive : (sectionsR U).Additive where
  map_add := by intros; rfl

/-- Sections over `U` through the slice adjunction. -/
abbrev sliceSections : (Spec R).Modules ⥤ ModuleCat R :=
  SheafOfModules.overFunctor (Spec R).ringCatSheaf U ⋙
    SheafOfModules.pushforward (SheafOfModules.pushforwardOver U) ⋙ moduleSpecΓFunctor

/-- The comparison morphism from the terminal object of the slice to the image of `⊤`. -/
def toStarTop : Over.mk (𝟙 U) ⟶ (Over.star U).obj ⊤ :=
  Over.homMk (prod.lift (𝟙 U) (homOfLE le_top)) (Subsingleton.elim _ _)

/-- The inverse comparison. -/
def fromStarTop : (Over.star U).obj ⊤ ⟶ Over.mk (𝟙 U) :=
  Over.homMk ((Over.star U).obj ⊤).hom (Subsingleton.elim _ _)

/-- On a thin category, the restriction maps of a presheaf of modules are semilinear along any
restriction map of the rings. -/
lemma presheafOfModules_map_smul_map_of_subsingleton {C : Type*} [Category C]
    [∀ X Y : C, Subsingleton (X ⟶ Y)] {S : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} S)
    {A B D : Cᵒᵖ} (q : A ⟶ B) (f : B ⟶ D) (p : A ⟶ D) (c : S.obj A) (x : M.obj B) :
    M.map f (S.map q c • x) = S.map p c • M.map f x := by
  rw [M.map_smul, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp,
    Subsingleton.elim (q ≫ f) p]

/-- The restriction map of a presheaf of modules along an identity is the identity. -/
lemma presheafOfModules_map_id_apply {C : Type*} [Category C] {S : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} S) (X : Cᵒᵖ) (x : M.obj X) : M.map (𝟙 X) x = x := by
  rw [M.map_id]
  rfl

/-- Scalar multiplication by `r : R` on sections over `U` is multiplication by the restriction to
`U` of the global section corresponding to `r`. -/
lemma smul_sectionsR (F : (Spec R).Modules) (r : R) (x : (sectionsR U).obj F) :
    r • x = ((Spec R).ringCatSheaf.obj.map (homOfLE le_top : U ⟶ ⊤).op
      ((Scheme.ΓSpecIso R).inv r)) • (show F.val.obj (op U) from x) := rfl

/-- Scalar multiplication by `r : R` on sections computed through the slice adjunction is
multiplication by a restriction of the global section corresponding to `r`. -/
lemma exists_smul_sliceSections (F : (Spec R).Modules) (r : R) (x : (sliceSections U).obj F) :
    ∃ q : ((Over.star U).obj ⊤).left ⟶ ⊤, r • x = ((Spec R).ringCatSheaf.obj.map q.op
      ((Scheme.ΓSpecIso R).inv r)) • (show F.val.obj (op ((Over.star U).obj ⊤).left) from x) :=
  ⟨_, rfl⟩

/-- Sections over `U` computed through the slice adjunction are sections over `U`. -/
def sliceSectionsIsoApp (F : (Spec R).Modules) : (sliceSections U).obj F ≅ (sectionsR U).obj F :=
  LinearEquiv.toModuleIso (show ((sliceSections U).obj F : Type u) ≃ₗ[R] (sectionsR U).obj F from
    { toFun := fun x => F.val.map (toStarTop U).left.op x
      invFun := fun y => F.val.map (fromStarTop U).left.op y
      map_add' := fun x y => map_add (F.val.map (toStarTop U).left.op).hom x y
      map_smul' := fun r x => by
        obtain ⟨q, hq⟩ := exists_smul_sliceSections U F r x
        exact (congrArg (fun y => F.val.map (toStarTop U).left.op y) hq).trans
          (presheafOfModules_map_smul_map_of_subsingleton F.val q.op _ (homOfLE le_top : U ⟶ ⊤).op
              _ _)
      left_inv := fun x =>
        ((F.val.map_comp_apply (toStarTop U).left.op (fromStarTop U).left.op
          (show F.val.obj (op ((Over.star U).obj ⊤).left) from x)).symm.trans
          (F.val.congr_map_apply (Subsingleton.elim _ (𝟙 _)) _)).trans
              (presheafOfModules_map_id_apply F.val _ _)
      right_inv := fun y =>
        ((F.val.map_comp_apply (fromStarTop U).left.op (toStarTop U).left.op
          (show F.val.obj (op U) from y)).symm.trans
          (F.val.congr_map_apply (Subsingleton.elim _ (𝟙 _)) _)).trans
              (presheafOfModules_map_id_apply F.val _ _) })

/-- The isomorphism `sliceSectionsIsoApp` is the restriction map along `toStarTop`. -/
lemma sliceSectionsIsoApp_hom_apply (F : (Spec R).Modules) (x : (sliceSections U).obj F) :
    (sliceSectionsIsoApp U F).hom x =
      F.val.map (toStarTop U).left.op (show F.val.obj (op ((Over.star U).obj ⊤).left) from x) :=
  rfl

/-- The functor `sliceSections` acts on a morphism by its component on the image of `⊤`. -/
lemma sliceSections_map_apply {F G : (Spec R).Modules} (h : F ⟶ G)
    (x : (sliceSections U).obj F) :
    (sliceSections U).map h x =
      h.val.app (op ((Over.star U).obj ⊤).left)
        (show F.val.obj (op ((Over.star U).obj ⊤).left) from x) :=
  rfl

/-- The functor `sectionsR U` acts on a morphism by its component at `U`. -/
lemma sectionsR_map_apply {F G : (Spec R).Modules} (h : F ⟶ G) (y : (sectionsR U).obj F) :
    (sectionsR U).map h y = h.val.app (op U) (show F.val.obj (op U) from y) :=
  rfl

/-- Sections over `U` computed through the slice adjunction are sections over `U`, naturally. -/
def sliceSectionsIso : sliceSections U ≅ sectionsR U :=
  NatIso.ofComponents (sliceSectionsIsoApp U) fun {F G} h => by
    ext x
    exact (PresheafOfModules.naturality_apply h.val (toStarTop U).left.op
      (show F.val.obj (op ((Over.star U).obj ⊤).left) from x)).symm

/-- **Morphisms out of the restriction of `M̃` to `U` are `R`-linear maps out of `M`.** For an
`R`-module `M`, an `𝒪_{Spec R}`-module `F` and an open `U`, morphisms `M̃|_U ⟶ F|_U` of modules on
the slice site over `U` correspond to `R`-linear maps `M ⟶ F(U)`. -/
def tildeOverHomEquiv (M : ModuleCat.{u} R) (F : (Spec R).Modules) :
    (((tilde.functor R).obj M).over U ⟶ F.over U) ≃ (M ⟶ (sectionsR U).obj F) :=
  (((SheafOfModules.overPushforwardOverAdj U).homEquiv _ _).trans
    (tilde.adjunction.homEquiv _ _)).trans ((sliceSectionsIso U).app F).homToEquiv

/-- The correspondence `tildeOverHomEquiv` evaluates a morphism at `U` on the image of `M`. -/
lemma tildeOverHomEquiv_apply (M : ModuleCat.{u} R) (F : (Spec R).Modules)
    (φ : ((tilde.functor R).obj M).over U ⟶ F.over U) (m : M) :
    tildeOverHomEquiv U M F φ m =
      φ.val.app (op (Over.mk (𝟙 U))) (tilde.toOpen M U m) := by
  have h1 : tildeOverHomEquiv U M F φ m =
      F.val.map (toStarTop U).left.op (φ.val.app (op ((Over.star U).obj ⊤))
        (((tilde.functor R).obj M).val.map (prod.snd : U ⨯ ⊤ ⟶ ⊤).op
          (tilde.toOpen M ⊤ m))) := rfl
  rw [h1]
  exact (PresheafOfModules.naturality_apply φ.val (toStarTop U).op
    (tilde.toOpen M ((Over.star U).obj ⊤).left m)).symm

/-- The correspondence `tildeOverHomEquiv` is additive. -/
lemma tildeOverHomEquiv_add (M : ModuleCat.{u} R) (F : (Spec R).Modules)
    (φ ψ : ((tilde.functor R).obj M).over U ⟶ F.over U) :
    tildeOverHomEquiv U M F (φ + ψ) = tildeOverHomEquiv U M F φ + tildeOverHomEquiv U M F ψ := by
  ext m
  rw [tildeOverHomEquiv_apply, ModuleCat.hom_add, LinearMap.add_apply, tildeOverHomEquiv_apply,
    tildeOverHomEquiv_apply]
  rfl

/-- `tildeOverHomEquiv` as an additive equivalence. -/
def tildeOverHomAddEquiv (M : ModuleCat.{u} R) (F : (Spec R).Modules) :
    (((tilde.functor R).obj M).over U ⟶ F.over U) ≃+ (M ⟶ (sectionsR U).obj F) :=
  { tildeOverHomEquiv U M F with map_add' := tildeOverHomEquiv_add U M F }

/-- The correspondence `tildeOverHomEquiv` is natural in the module `F`. -/
lemma tildeOverHomEquiv_comp_right (M : ModuleCat.{u} R) {F G : (Spec R).Modules}
    (φ : ((tilde.functor R).obj M).over U ⟶ F.over U) (h : F ⟶ G) :
    tildeOverHomEquiv U M G (φ ≫ h.over U) = tildeOverHomEquiv U M F φ ≫ (sectionsR U).map h := by
  ext m
  rw [tildeOverHomEquiv_apply, ModuleCat.comp_apply, tildeOverHomEquiv_apply]
  rfl

/-- The correspondence `tildeOverHomEquiv` is natural in the module `M`. -/
lemma tildeOverHomEquiv_comp_left {M N : ModuleCat.{u} R} (F : (Spec R).Modules) (g : M ⟶ N)
    (φ : ((tilde.functor R).obj N).over U ⟶ F.over U) :
    tildeOverHomEquiv U M F (((tilde.functor R).map g).over U ≫ φ) =
      g ≫ tildeOverHomEquiv U N F φ := by
  ext m
  rw [tildeOverHomEquiv_apply, ModuleCat.comp_apply, tildeOverHomEquiv_apply]
  exact congrArg (φ.val.app (op (Over.mk (𝟙 U))))
    (ConcreteCategory.congr_hom (tilde.toOpen_map_app g U) m)

/-- **The Hom complex out of the restriction of `Ã` to `U`.** For a complex `A` of `R`-modules
and a complex `I` of `𝒪_{Spec R}`-modules, the Hom complex from `Ã|_U` to `I|_U` on the slice
site over `U` is the Hom complex of `R`-modules from `A` to the sections of `I` over `U`. -/
def homComplexTildeOverIso (A : CochainComplex (ModuleCat.{u} R) ℤ)
    (I : CochainComplex (Spec R).Modules ℤ) :
    CochainComplex.HomComplex
        (((SheafOfModules.overFunctor (Spec R).ringCatSheaf U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj A))
        (((SheafOfModules.overFunctor (Spec R).ringCatSheaf U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      CochainComplex.HomComplex A (((sectionsR U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I) :=
  CochainComplex.HomComplex.homComplexIsoOfAddEquiv
    (fun p q => tildeOverHomAddEquiv U (A.X p) (I.X q))
    (fun p q q' f => tildeOverHomEquiv_comp_right U (A.X p) f (I.d q q'))
    (fun p' p q f => tildeOverHomEquiv_comp_left U (I.X q) (A.d p' p) f)

end AlgebraicGeometry.TildeSlice
