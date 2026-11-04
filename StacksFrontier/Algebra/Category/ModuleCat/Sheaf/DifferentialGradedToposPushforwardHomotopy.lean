module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransportHomotopy

/-!
# The direct image on homotopy categories, and base change up to homotopy

Let `f : X ⟶ Y` be a morphism of ringed topoi, let `B` be a sheaf of differential graded
`O_X`-algebras, let `A` be a sheaf of differential graded `O_Y`-algebras and let `ψ : A ⟶ f_*B` be
a unital homomorphism. The direct image `f_{*,ψ} : Mod^dg(B) ⥤ Mod^dg(A)` carries homotopic
morphisms to homotopic morphisms, so it descends to the homotopy categories, `K(B) ⥤ K(A)`.

If `T` is a base change of a right differential graded `A`-module `P`, that is, `T` corepresents
`Q ↦ Hom_A(P, f_{*,ψ}Q)`, then two morphisms out of `T` are homotopic exactly when their
transposes are, so the bijection of the base change descends to a bijection of homotopy classes

`Hom_{K(B)}(T, Q) ≃ Hom_{K(A)}(P, f_{*,ψ}Q)`,

natural in `Q`. The point is that a homotopy is a homomorphism of graded modules into the shift
down by one whose commutator with the differentials is the difference of the two morphisms, and
the base change transports such homomorphisms together with their commutators
(`SheafOfModules.DifferentialGradedModule.toposShiftDownEquiv` and
`SheafOfModules.DifferentialGradedModule.deltaHom_toposShiftDownEquiv`).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyToposPushforward`: **the direct image
  `K(B) ⥤ K(A)` on homotopy categories.**
* `SheafOfModules.DifferentialGradedModule.Homotopy.shiftDownHom` and
  `SheafOfModules.DifferentialGradedModule.homotopyOfDeltaHom` pass between a homotopy and a
  homomorphism of graded modules into the shift down by one.
* `SheafOfModules.DifferentialGradedModule.homotopyHomEquiv`: **the bijection of homotopy classes
  `Hom_{K(B)}(T, Q) ≃ Hom_{K(A)}(P, f_{*,ψ}Q)` attached to a base change `T` of `P`.**

## Main results

* `SheafOfModules.DifferentialGradedModule.preservesHomotopic_restrictScalars` and
  `preservesHomotopic_toposPushforward`: restriction of scalars and the direct image carry
  homotopic morphisms to homotopic morphisms; both are additive functors.
* `SheafOfModules.DifferentialGradedModule.quotient_comp_homotopyToposPushforward`: the direct
  image on homotopy categories factors the direct image through the two quotient functors.
* `SheafOfModules.DifferentialGradedModule.homotopic_iff_exists_deltaHom`: two morphisms are
  homotopic exactly when their difference is the commutator of the differentials with a
  homomorphism of graded modules into the shift down by one.
* `SheafOfModules.DifferentialGradedModule.toposHomEquiv_sub`: transposition through a base change
  is additive.
* `SheafOfModules.DifferentialGradedModule.homotopic_homEquiv_iff`: **two morphisms out of a base
  change are homotopic exactly when their transposes are.**
* `SheafOfModules.DifferentialGradedModule.homotopyHomEquiv_map` and `homotopyHomEquiv_comp`: the
  bijection sends the class of a morphism to the class of its transpose, and it is natural in the
  target for every morphism of the homotopy category.

## References

* [Stacks Project, Tag 0FS1](https://stacks.math.columbia.edu/tag/0FS1)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w v₁ u₁ v₂ u₂ t a m v u

namespace SheafOfModules.DifferentialGradedModule

section RestrictScalars

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-- **Restriction of scalars carries a homotopy to a homotopy**: the same degree `-1` maps, the
action of `A` being the action of `B` through `φ`. -/
def restrictScalarsHomotopy (φ : A ⟶ B) (hφ : φ.IsUnital)
    {M N : DifferentialGradedModule.{t, a, m} B} {f g : M ⟶ N} (h : Homotopy f g) :
    Homotopy ((restrictScalars φ hφ).map f) ((restrictScalars φ hφ).map g) where
  app := h.app
  map_mul n i U x y := h.map_mul n i U x ((φ.toHomologicalComplex.f i).val.app U y)
  comm := h.comm

/-- **Restriction of scalars carries homotopic morphisms to homotopic morphisms.** -/
theorem preservesHomotopic_restrictScalars (φ : A ⟶ B) (hφ : φ.IsUnital) :
    PreservesHomotopic (restrictScalars.{t, a, m} φ hφ) :=
  fun _ _ ⟨h⟩ ↦ ⟨restrictScalarsHomotopy φ hφ h⟩

/-- Restriction of scalars is an additive functor: it does not change the underlying maps. -/
instance restrictScalars_additive (φ : A ⟶ B) (hφ : φ.IsUnital) :
    (restrictScalars.{t, a, m} φ hφ).Additive where
  map_add := Hom.ext fun _ ↦ rfl

end RestrictScalars

section ShiftDownBridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {M N : DifferentialGradedModule.{t, a, m} A}

/-- **The homomorphism of graded modules into the shift down underlying a homotopy**: a homotopy
is a degree `-1` map of graded modules, that is, a homomorphism of graded modules `M ⟶ N[-1]`. -/
noncomputable def Homotopy.shiftDownHom {f g : M ⟶ N} (h : Homotopy f g) :
    GradedModule.Hom (GradedModule.ofDifferentialGraded M) (gradedShiftDown N) where
  app := h.app
  map_smul n i U x y :=
    eq_of_heq ((h.map_mul n i U x y).trans (gradedShiftDown_smul_eval_heq N n i U _ y).symm)

/-- The components of `Homotopy.shiftDownHom` are those of the homotopy. -/
@[simp]
theorem Homotopy.shiftDownHom_app {f g : M ⟶ N} (h : Homotopy f g) (n : ℤ) :
    h.shiftDownHom.app n = h.app n :=
  rfl

/-- **The commutator of the differentials with the homomorphism underlying a homotopy between
`f` and `g` is `f - g`**: that is the homotopy equation. -/
theorem deltaHom_shiftDownHom {f g : M ⟶ N} (h : Homotopy f g) :
    deltaHom h.shiftDownHom = f - g := by
  refine Hom.ext fun n ↦ ?_
  rw [deltaHom_f, sub_f, h.comm, deltaFamily, ofShiftDownHom_eq, Category.assoc]
  rfl

/-- **A homomorphism of graded modules `M ⟶ N[-1]` whose commutator with the differentials is
`f - g` is a homotopy between `f` and `g`.** -/
noncomputable def homotopyOfDeltaHom {f g : M ⟶ N}
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded M) (gradedShiftDown N))
    (hΦ : deltaHom Φ = f - g) : Homotopy f g where
  app n := shiftDownApp Φ n
  map_mul n i U x y :=
    (heq_of_eq (Φ.map_smul n i U x y)).trans (gradedShiftDown_smul_eval_heq N n i U _ y)
  comm n := by
    have hn := congrArg (fun z : M ⟶ N ↦ z.toHomologicalComplex.f n) hΦ
    simp only [deltaHom_f, sub_f] at hn
    rw [← hn, deltaFamily, ofShiftDownHom_eq, Category.assoc]

/-- The components of `homotopyOfDeltaHom Φ hΦ` are those of `Φ`. -/
@[simp]
theorem homotopyOfDeltaHom_app {f g : M ⟶ N}
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded M) (gradedShiftDown N))
    (hΦ : deltaHom Φ = f - g) (n : ℤ) :
    (homotopyOfDeltaHom Φ hΦ).app n = Φ.app n :=
  rfl

/-- **Two morphisms are homotopic exactly when their difference is the commutator of the
differentials with a homomorphism of graded modules into the shift down by one.** -/
theorem homotopic_iff_exists_deltaHom (f g : M ⟶ N) :
    Homotopic f g ↔
      ∃ Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded M) (gradedShiftDown N),
        deltaHom Φ = f - g :=
  ⟨fun ⟨h⟩ ↦ ⟨h.shiftDownHom, deltaHom_shiftDownHom h⟩,
    fun ⟨Φ, hΦ⟩ ↦ ⟨homotopyOfDeltaHom Φ hΦ⟩⟩

end ShiftDownBridge

section ToposPushforward

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)

/-- **The direct image is an additive functor**: it is `G` applied degreewise. -/
instance toposPushforward_additive : (toposPushforward G ψ hψ).Additive where
  map_add {_ _ f g} := Hom.ext fun n ↦ G.map_add (f := f.toHomologicalComplex.f n)
    (g := g.toHomologicalComplex.f n)

/-- **The direct image carries homotopic morphisms to homotopic morphisms**: the transport along
`G` does, and so does restriction of scalars along `ψ`. -/
theorem preservesHomotopic_toposPushforward : PreservesHomotopic (toposPushforward G ψ hψ) :=
  PreservesHomotopic.comp (preservesHomotopic_transportFunctor G _ _)
    (preservesHomotopic_restrictScalars ψ hψ)

/-- **The direct image `K(B) ⥤ K(A)` on homotopy categories.** -/
noncomputable def homotopyToposPushforward :
    HomotopyCategory.{w, w, w} B ⥤ HomotopyCategory.{w, w, w} A :=
  HomotopyCategory.descend (toposPushforward G ψ hψ) (preservesHomotopic_toposPushforward G ψ hψ)

/-- The direct image on homotopy categories factors the direct image through the two quotient
functors. -/
theorem quotient_comp_homotopyToposPushforward :
    HomotopyCategory.quotient B ⋙ homotopyToposPushforward G ψ hψ =
      toposPushforward G ψ hψ ⋙ HomotopyCategory.quotient A :=
  HomotopyCategory.quotient_comp_descend _ _

/-- The direct image on homotopy categories sends the class of `Q` to the class of its direct
image. -/
@[simp]
theorem homotopyToposPushforward_obj (Q : DifferentialGradedModule.{w, w, w} B) :
    (homotopyToposPushforward G ψ hψ).obj ((HomotopyCategory.quotient B).obj Q) =
      (HomotopyCategory.quotient A).obj ((toposPushforward G ψ hψ).obj Q) :=
  rfl

/-- The direct image on homotopy categories sends the class of `q` to the class of its direct
image. -/
@[simp]
theorem homotopyToposPushforward_map {Q Q' : DifferentialGradedModule.{w, w, w} B}
    (q : Q ⟶ Q') :
    (homotopyToposPushforward G ψ hψ).map ((HomotopyCategory.quotient B).map q) =
      (HomotopyCategory.quotient A).map ((toposPushforward G ψ hψ).map q) :=
  rfl

/-! ### Homotopy classes through a base change -/

section BaseChange

variable {P : DifferentialGradedModule.{w, w, w} A} {T : DifferentialGradedModule.{w, w, w} B}
  (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)

/-- **The transpose of a morphism out of a base change is the transpose of the identity followed
by the direct image of that morphism.** -/
theorem toposHomEquiv_eq {Q : DifferentialGradedModule.{w, w, w} B} (a : T ⟶ Q) :
    (e.homEquiv a : P ⟶ (toposPushforward G ψ hψ).obj Q) =
      e.homEquiv (𝟙 T) ≫ (toposPushforward G ψ hψ).map a :=
  (congrArg e.homEquiv (Category.id_comp a).symm).trans (e.homEquiv_comp a _)

/-- **Transposition through a base change is additive.** -/
theorem toposHomEquiv_sub {Q : DifferentialGradedModule.{w, w, w} B} (a b : T ⟶ Q) :
    e.homEquiv (a - b) = @HSub.hSub (P ⟶ (toposPushforward G ψ hψ).obj Q)
      (P ⟶ (toposPushforward G ψ hψ).obj Q) (P ⟶ (toposPushforward G ψ hψ).obj Q) _
      (e.homEquiv a) (e.homEquiv b) := by
  rw [toposHomEquiv_eq G ψ hψ e, toposHomEquiv_eq G ψ hψ e a, toposHomEquiv_eq G ψ hψ e b,
    Functor.map_sub, Preadditive.comp_sub]

/-- The inverse transposition through a base change is additive. -/
theorem toposHomEquiv_symm_sub {Q : DifferentialGradedModule.{w, w, w} B}
    (c c' : P ⟶ (toposPushforward G ψ hψ).obj Q) :
    e.homEquiv.symm (c - c') = e.homEquiv.symm c - e.homEquiv.symm c' := by
  refine e.homEquiv.injective ((Equiv.apply_symm_apply _ _).trans ?_)
  rw [toposHomEquiv_sub G ψ hψ e, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Two morphisms out of a base change are homotopic exactly when their transposes are.** A
homotopy is a homomorphism of graded modules into the shift down by one whose commutator with the
differentials is the difference, and the base change of such a homomorphism,
`SheafOfModules.DifferentialGradedModule.toposShiftDownEquiv`, is a bijection which carries that
commutator across. -/
theorem homotopic_homEquiv_iff {Q : DifferentialGradedModule.{w, w, w} B} (a b : T ⟶ Q) :
    Homotopic (e.homEquiv a : P ⟶ (toposPushforward G ψ hψ).obj Q) (e.homEquiv b) ↔
      Homotopic a b := by
  rw [homotopic_iff_exists_deltaHom, homotopic_iff_exists_deltaHom,
    ← toposHomEquiv_sub G ψ hψ e]
  constructor
  · rintro ⟨Ψ, hΨ⟩
    refine ⟨(toposShiftDownEquiv G ψ hψ e Q).symm Ψ, e.homEquiv.injective ?_⟩
    rwa [← deltaHom_toposShiftDownEquiv, Equiv.apply_symm_apply]
  · rintro ⟨Φ, hΦ⟩
    refine ⟨toposShiftDownEquiv G ψ hψ e Q Φ, ?_⟩
    rw [deltaHom_toposShiftDownEquiv, hΦ]

/-- Two morphisms into the direct image are homotopic exactly when their inverse transposes
through a base change are. -/
theorem homotopic_homEquiv_symm_iff {Q : DifferentialGradedModule.{w, w, w} B}
    (c c' : P ⟶ (toposPushforward G ψ hψ).obj Q) :
    Homotopic (e.homEquiv.symm c) (e.homEquiv.symm c') ↔ Homotopic c c' := by
  rw [← homotopic_homEquiv_iff G ψ hψ e, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- A map preserving and reflecting homotopy sends a morphism and a representative of its class
to the same class. -/
private theorem quotient_map_preimage_map_eq
    {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁} {R₁ : Sheaf J₁ RingCat.{w}}
    {A₁ : DifferentialGradedAlgebra.{w, w} R₁} {M₁ N₁ : DifferentialGradedModule.{w, w, w} A₁}
    {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂} {R₂ : Sheaf J₂ RingCat.{w}}
    {A₂ : DifferentialGradedAlgebra.{w, w} R₂} {M₂ N₂ : DifferentialGradedModule.{w, w, w} A₂}
    (s : (M₁ ⟶ N₁) → (M₂ ⟶ N₂)) (hs : ∀ a b, Homotopic (s a) (s b) ↔ Homotopic a b)
    (a : M₁ ⟶ N₁) :
    (HomotopyCategory.quotient A₂).map
        (s ((HomotopyCategory.quotient A₁).preimage ((HomotopyCategory.quotient A₁).map a))) =
      (HomotopyCategory.quotient A₂).map (s a) :=
  (HomotopyCategory.quotient_map_eq_iff _ _).2 ((hs _ _).2
    ((HomotopyCategory.quotient_map_eq_iff _ _).1 (Functor.map_preimage _ _)))

/-- The forward map of `homotopyHomEquiv`: the homotopy class of the transpose of a
representative. -/
noncomputable def homotopyHomEquivFun (Q : DifferentialGradedModule.{w, w, w} B)
    (φ : (HomotopyCategory.quotient B).obj T ⟶ (HomotopyCategory.quotient B).obj Q) :
    (HomotopyCategory.quotient A).obj P ⟶
      (homotopyToposPushforward G ψ hψ).obj ((HomotopyCategory.quotient B).obj Q) :=
  (HomotopyCategory.quotient A).map (e.homEquiv ((HomotopyCategory.quotient B).preimage φ))

/-- The inverse map of `homotopyHomEquiv`: the homotopy class of the inverse transpose of a
representative. -/
noncomputable def homotopyHomEquivInv (Q : DifferentialGradedModule.{w, w, w} B)
    (φ : (HomotopyCategory.quotient A).obj P ⟶
      (homotopyToposPushforward G ψ hψ).obj ((HomotopyCategory.quotient B).obj Q)) :
    (HomotopyCategory.quotient B).obj T ⟶ (HomotopyCategory.quotient B).obj Q :=
  (HomotopyCategory.quotient B).map
    (e.homEquiv.symm ((HomotopyCategory.quotient A).preimage φ))

/-- `homotopyHomEquivFun` sends the class of `a` to the class of its transpose. -/
theorem homotopyHomEquivFun_map {Q : DifferentialGradedModule.{w, w, w} B} (a : T ⟶ Q) :
    homotopyHomEquivFun G ψ hψ e Q ((HomotopyCategory.quotient B).map a) =
      (HomotopyCategory.quotient A).map (e.homEquiv a) := by
  exact quotient_map_preimage_map_eq _ (homotopic_homEquiv_iff G ψ hψ e) a

/-- `homotopyHomEquivInv` sends the class of `c` to the class of its inverse transpose. -/
theorem homotopyHomEquivInv_map {Q : DifferentialGradedModule.{w, w, w} B}
    (c : P ⟶ (toposPushforward G ψ hψ).obj Q) :
    homotopyHomEquivInv G ψ hψ e Q ((HomotopyCategory.quotient A).map c) =
      (HomotopyCategory.quotient B).map (e.homEquiv.symm c) := by
  exact quotient_map_preimage_map_eq _ (homotopic_homEquiv_symm_iff G ψ hψ e) c

/-- **The adjunction between base change and the direct image, up to homotopy**: homotopy classes
of morphisms out of a base change `T` of `P` are homotopy classes of morphisms from `P` into the
direct image. -/
noncomputable def homotopyHomEquiv (Q : DifferentialGradedModule.{w, w, w} B) :
    ((HomotopyCategory.quotient B).obj T ⟶ (HomotopyCategory.quotient B).obj Q) ≃
      ((HomotopyCategory.quotient A).obj P ⟶
        (homotopyToposPushforward G ψ hψ).obj ((HomotopyCategory.quotient B).obj Q)) where
  toFun := homotopyHomEquivFun G ψ hψ e Q
  invFun := homotopyHomEquivInv G ψ hψ e Q
  left_inv φ := by
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient B).map_surjective φ
    rw [homotopyHomEquivFun_map, homotopyHomEquivInv_map, Equiv.symm_apply_apply]
  right_inv φ := by
    obtain ⟨c, rfl⟩ := (HomotopyCategory.quotient A).map_surjective φ
    rw [homotopyHomEquivInv_map, homotopyHomEquivFun_map, Equiv.apply_symm_apply]

/-- **On the class of a morphism, the bijection is the class of its transpose.** -/
@[simp]
theorem homotopyHomEquiv_map {Q : DifferentialGradedModule.{w, w, w} B} (a : T ⟶ Q) :
    homotopyHomEquiv G ψ hψ e Q ((HomotopyCategory.quotient B).map a) =
      (HomotopyCategory.quotient A).map (e.homEquiv a) :=
  homotopyHomEquivFun_map G ψ hψ e a

/-- On the class of a morphism, the inverse bijection is the class of its inverse transpose. -/
@[simp]
theorem homotopyHomEquiv_symm_map {Q : DifferentialGradedModule.{w, w, w} B}
    (c : P ⟶ (toposPushforward G ψ hψ).obj Q) :
    (homotopyHomEquiv G ψ hψ e Q).symm ((HomotopyCategory.quotient A).map c) =
      (HomotopyCategory.quotient B).map (e.homEquiv.symm c) :=
  homotopyHomEquivInv_map G ψ hψ e c

/-- **The bijection is natural in the target**, for any morphism of the homotopy category. -/
theorem homotopyHomEquiv_comp {Q Q' : DifferentialGradedModule.{w, w, w} B}
    (φ : (HomotopyCategory.quotient B).obj T ⟶ (HomotopyCategory.quotient B).obj Q)
    (v : (HomotopyCategory.quotient B).obj Q ⟶ (HomotopyCategory.quotient B).obj Q') :
    homotopyHomEquiv G ψ hψ e Q' (φ ≫ v) =
      homotopyHomEquiv G ψ hψ e Q φ ≫ (homotopyToposPushforward G ψ hψ).map v := by
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient B).map_surjective φ
  obtain ⟨q, rfl⟩ := (HomotopyCategory.quotient B).map_surjective v
  rw [← Functor.map_comp, homotopyHomEquiv_map, homotopyHomEquiv_map, e.homEquiv_comp,
    homotopyToposPushforward_map]
  exact (HomotopyCategory.quotient A).map_comp _ _

/-- The inverse bijection is natural in the target. -/
theorem homotopyHomEquiv_symm_comp {Q Q' : DifferentialGradedModule.{w, w, w} B}
    (φ : (HomotopyCategory.quotient A).obj P ⟶
      (homotopyToposPushforward G ψ hψ).obj ((HomotopyCategory.quotient B).obj Q))
    (v : (HomotopyCategory.quotient B).obj Q ⟶ (HomotopyCategory.quotient B).obj Q') :
    (homotopyHomEquiv G ψ hψ e Q').symm (φ ≫ (homotopyToposPushforward G ψ hψ).map v) =
      (homotopyHomEquiv G ψ hψ e Q).symm φ ≫ v := by
  rw [Equiv.symm_apply_eq, homotopyHomEquiv_comp, Equiv.apply_symm_apply]

end BaseChange

end ToposPushforward

end SheafOfModules.DifferentialGradedModule

end
