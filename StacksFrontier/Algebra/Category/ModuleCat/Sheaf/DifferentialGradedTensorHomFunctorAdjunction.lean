module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomAdjunction

/-!
# The tensor product is left adjoint to the internal hom, for sheaves of differential graded
modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` and `B` be sheaves of differential graded
`R`-algebras and let `N` be a differential graded `(A, B)`-bimodule. Then

`- ⊗_A N : Mod(A, d) ⥤ Mod(B, d)`  is left adjoint to
`SheafHom^dg_B(N, -) : Mod(B, d) ⥤ Mod(A, d)`,

the bijection being `φ ↦ (x ↦ (y ↦ φ (x ⊗ y)))` on local sections.

## Main definitions

* `SheafOfModules.LocalHom.diff` is the differential `d(f) = d_L ∘ f - f ∘ d_K` of a degree-zero
  local homomorphism of right differential graded modules, a degree-one local homomorphism.
* `SheafOfModules.LocalHom.ofHom` reads a morphism of right differential graded modules as a
  degree-zero local homomorphism over an object of the site, and
  `SheafOfModules.DifferentialGradedModule.homOfLocal` assembles a compatible family of
  degree-zero local homomorphisms with vanishing differential into a morphism.
* `SheafOfModules.tensorHomLocalEquiv` identifies the degree-`n` local homomorphisms
  `M ⊗_A N|_U → L|_U` with the degree-`n` local homomorphisms `M|_U → SheafHom^dg_B(N, L)|_U`.
* `SheafOfModules.tensorHomEquivDg` is the bijection between the morphisms `M ⊗_A N ⟶ L` of
  right differential graded `B`-modules and the morphisms `M ⟶ SheafHom^dg_B(N, L)` of right
  differential graded `A`-modules.
* `SheafOfModules.tensorSheafHomAdjunction` is the resulting adjunction between a tensor product
  functor and an internal hom functor.

## Main results

* `SheafOfModules.LocalHom.diff_tensorHomLocalEquiv`: the local identification commutes with the
  differential of local homomorphisms. This is what makes it carry chain maps to chain maps in
  both directions, and it is the differential graded content of the adjunction.
* `SheafOfModules.tensorHomEquivDg_eval`: the bijection on morphisms is
  `φ ↦ (x ↦ (y ↦ φ (x ⊗ y)))`.

## Implementation notes

The tensor product and the internal hom cannot be written down by a formula over a general
ringed site, so they are used through `SheafOfModules.IsTensorProduct` and
`SheafOfModules.IsSheafHom`, which pin them by their universal properties, and through the
carriers `SheafOfModules.TensorFunctorData` and `SheafOfModules.SheafHomFunctorData` for the
functors. The adjunction is a consequence of those universal properties and is proved here, not
assumed.

The identification of the local homomorphisms is the composite of the universal property of the
tensor product with the local tensor-hom identification
`SheafOfModules.balancedEquivDg` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensorHomAdjunction.lean`, both
of which go through the `A`-balanced bilinear families of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensor.lean`. What has to be
added is the behaviour of that identification under the differential, and the passage from local
homomorphisms over every object of the site to morphisms over the site, which is the
differential graded analogue of `SheafOfModules.GradedHomOfDegree.ofLocal`.

Only degree-zero local homomorphisms are given a differential. In degree `n` the differential
`d(f) = d_L ∘ f - (-1)^n f ∘ d_K` of a homomorphism of right differential graded modules is again
`A`-linear, but the two signs produced by the Leibniz rule cancel only after the sign `(-1)^n` is
taken into account; for `n = 0` the computation is the one below, and that is the only degree the
adjunction uses.

The universes of the site and of its morphisms, of the sheaf of rings, of the homogeneous
components of the two algebras and of the bimodule, and of the modules on the `A`-side and on
the `B`-side are independent; the two algebras share a sheaf of rings and a component universe
because the bimodule relates them. The module `M` and the internal hom share a universe, as in
the file of the local identification.

## References

* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
-/

@[expose] public section

open CategoryTheory

universe t a w z s v u

namespace SheafOfModules

/-! ### The differential of a degree-zero local homomorphism -/

section Diff

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {K : DifferentialGradedModule.{t, a, w} A}
  {L : DifferentialGradedModule.{t, a, z} A}

/-- The differential `d(f) = d_L ∘ f - f ∘ d_K` of a degree-zero local homomorphism of right
differential graded modules, a degree-one local homomorphism. -/
def LocalHom.diff {U : C} (f : LocalHom K L 0 U) : LocalHom K L 1 U where
  app i j hij V :=
    (homSections (L.complex.d i j) (Opposite.op V.left)).comp (f.app i i (add_zero i) V) -
      (f.app j j (add_zero j) V).comp (homSections (K.complex.d i j) (Opposite.op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      f.map_smul, homSections_smul, smul_sub]
  naturality i j hij {V W} q x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [map_sub_sections]
    simp only [homSections_naturality, f.naturality]
    rfl
  isLinear i j hij p V x b := by
    subst hij
    have hd : i + p + 1 = i + 1 + p := by omega
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      homSections_apply, map_sub]
    rw [f.isLinear i i (add_zero i) p V x b,
      d_app_castHom L.complex hd (Opposite.op V.left),
      L.leibniz_castHom i p (Opposite.op V.left) (f.app i i (add_zero i) V x) b,
      d_app_castHom K.complex hd (Opposite.op V.left),
      K.leibniz_castHom i p (Opposite.op V.left) x b]
    simp only [map_add, map_zsmul, castHom_castHom, castHom_self]
    rw [LocalGradedHom.app_castHom f.toLocalGradedHom ((add_assoc i p 1).symm.trans hd) V _,
      f.isLinear (i + 1) (i + 1) (add_zero (i + 1)) p V
        ((K.complex.d i (i + 1)).val.app (Opposite.op V.left) x) b,
      f.isLinear i i (add_zero i) (p + 1) V x
        ((A.complex.d p (p + 1)).val.app (Opposite.op V.left) b)]
    abel

/-- The differential of a degree-zero local homomorphism acts on a local section `x` by
`d (f x) - f (d x)`. -/
@[simp]
theorem LocalHom.diff_app {U : C} (f : LocalHom K L 0 U) (i j : ℤ) (hij : i + 1 = j)
    (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    f.diff.app i j hij V x =
      (L.complex.d i j).val.app (Opposite.op V.left) (f.app i i (add_zero i) V x) -
        f.app j j (add_zero j) V ((K.complex.d i j).val.app (Opposite.op V.left) x) :=
  rfl

/-- A degree-zero local homomorphism has vanishing differential exactly when it commutes with
the differentials of the two modules. -/
theorem LocalHom.diff_eq_zero_iff {U : C} (f : LocalHom K L 0 U) :
    f.diff = LocalHom.zero K L 1 U ↔
      ∀ (i j : ℤ) (_hij : i + 1 = j) (V : Over U)
        (x : (K.complex.X i).val.obj (Opposite.op V.left)),
        (L.complex.d i j).val.app (Opposite.op V.left) (f.app i i (add_zero i) V x) =
          f.app j j (add_zero j) V ((K.complex.d i j).val.app (Opposite.op V.left) x) := by
  refine ⟨fun h i j hij V x => ?_, fun h => LocalHom.ext fun i j hij V x => ?_⟩
  · have hx := LocalHom.app_congr h i j hij V x
    rw [LocalHom.zero_app, LocalHom.diff_app] at hx
    exact sub_eq_zero.mp hx
  · rw [LocalHom.zero_app, LocalHom.diff_app, h i j hij V x, sub_self]

end Diff

/-! ### Morphisms and compatible families of degree-zero local homomorphisms -/

section Assemble

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {K L : DifferentialGradedModule.{t, a, w} A}

/-- A morphism of right differential graded modules, read as a degree-zero local homomorphism
over an object of the site. -/
def LocalHom.ofHom (ψ : K ⟶ L) (U : C) : LocalHom K L 0 U where
  app i j hij V := (castHom L.complex.X ((add_zero i).symm.trans hij) (Opposite.op V.left)).comp
    (homSections (ψ.toHomologicalComplex.f i) (Opposite.op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, homSections_smul, castHom_smul]
  naturality i j hij {V W} g x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [castHom_naturality, homSections_naturality]
    rfl
  isLinear i j hij p V x b := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, homSections_apply]
    rw [ψ.map_mul i p (Opposite.op V.left) x b, mul_app_castHom]

/-- A morphism read as a local homomorphism acts on local sections through its degree-`i`
component, transported to the degree the local homomorphism is indexed by. -/
@[simp]
theorem LocalHom.ofHom_app (ψ : K ⟶ L) (U : C) (i j : ℤ) (hij : i + 0 = j) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.ofHom ψ U).app i j hij V x =
      castHom L.complex.X ((add_zero i).symm.trans hij) (Opposite.op V.left)
        ((ψ.toHomologicalComplex.f i).val.app (Opposite.op V.left) x) :=
  rfl

/-- The local homomorphisms read off a morphism are compatible with restriction along a
morphism of the site. -/
theorem LocalHom.restrict_ofHom (ψ : K ⟶ L) {U U' : C} (g : U' ⟶ U) :
    (LocalHom.ofHom ψ U).restrict g = LocalHom.ofHom ψ U' :=
  rfl

/-- The local homomorphism read off a morphism commutes with the differentials. -/
theorem LocalHom.diff_ofHom (ψ : K ⟶ L) (U : C) :
    (LocalHom.ofHom ψ U).diff = LocalHom.zero K L 1 U := by
  refine (LocalHom.ofHom ψ U).diff_eq_zero_iff.2 fun i j hij V x => ?_
  simp only [LocalHom.ofHom_app, castHom_self]
  exact homSections_congr (ψ.toHomologicalComplex.comm i j) (Opposite.op V.left) x

namespace DifferentialGradedModule

/-- The map on sections over an object of the site underlying a compatible family of degree-zero
local homomorphisms, one over each object of the site. -/
def localSections (f : ∀ U : C, LocalHom K L 0 U) (k : ℤ) (U : Cᵒᵖ) :
    (K.complex.X k).val.obj U →+ (L.complex.X k).val.obj U :=
  (f U.unop).app k k (add_zero k) (Over.mk (𝟙 U.unop))

/-- A compatible family of degree-zero local homomorphisms commutes with restriction. -/
theorem localSections_naturality {f : ∀ U : C, LocalHom K L 0 U}
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U') (k : ℤ) {U V : Cᵒᵖ} (γ : U ⟶ V)
    (x : (K.complex.X k).val.obj U) :
    (L.complex.X k).val.map γ (localSections f k U x) =
      localSections f k V ((K.complex.X k).val.map γ x) := by
  refine ((f U.unop).naturality k k (add_zero k)
    (Over.homMk γ.unop (Category.comp_id γ.unop) :
      Over.mk γ.unop ⟶ Over.mk (𝟙 U.unop)) x).trans ?_
  refine (LocalGradedHom.app_mk_congr (f U.unop).toLocalGradedHom k k (add_zero k)
    (Category.id_comp γ.unop).symm ((K.complex.X k).val.map γ x)).trans ?_
  exact LocalHom.app_congr (hf γ.unop) k k (add_zero k) (Over.mk (𝟙 V.unop)) _

/-- The degreewise morphism of sheaves of modules given by a compatible family of degree-zero
local homomorphisms. -/
def localHomDegree {f : ∀ U : C, LocalHom K L 0 U}
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U') (k : ℤ) :
    K.complex.X k ⟶ L.complex.X k where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => localSections f k U x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x =>
            (f U.unop).map_smul k k (add_zero k) (Over.mk (𝟙 U.unop)) r x }
      naturality := fun {_U _V} γ => ModuleCat.hom_ext (LinearMap.ext fun x =>
        (localSections_naturality hf k γ x).symm) }

/-- The degreewise morphism assembled from a compatible family acts on local sections over an
object of the site through the member of the family over that object. -/
@[simp]
theorem localHomDegree_apply {f : ∀ U : C, LocalHom K L 0 U}
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U') (k : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X k).val.obj U) :
    (localHomDegree hf k).val.app U x = (f U.unop).app k k (add_zero k) (Over.mk (𝟙 U.unop)) x :=
  rfl

/-- Assemble a compatible family of degree-zero local homomorphisms with vanishing differential,
one over each object of the site, into a morphism of right differential graded modules. -/
def homOfLocal {f : ∀ U : C, LocalHom K L 0 U}
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U')
    (hd : ∀ U : C, (f U).diff = LocalHom.zero K L 1 U) : K ⟶ L where
  toHomologicalComplex :=
    { f := fun k => localHomDegree hf k
      comm' := fun i j hij => by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
          ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
        exact (f U.unop).diff_eq_zero_iff.1 (hd U.unop) i j hij (Over.mk (𝟙 U.unop)) x }
  map_mul n i U x y := (f U.unop).isLinear n n (add_zero n) i (Over.mk (𝟙 U.unop)) x y

/-- Assembling a compatible family of degree-zero local homomorphisms and reading the morphism
back as local homomorphisms returns the family. -/
theorem ofHom_homOfLocal {f : ∀ U : C, LocalHom K L 0 U}
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U')
    (hd : ∀ U : C, (f U).diff = LocalHom.zero K L 1 U) (U : C) :
    LocalHom.ofHom (homOfLocal hf hd) U = f U := by
  refine LocalHom.ext fun i j hij V x => ?_
  obtain rfl : i = j := by omega
  rw [LocalHom.ofHom_app, castHom_self]
  show (f V.left).app i i (add_zero i) (Over.mk (𝟙 V.left)) x = (f U).app i i hij V x
  refine Eq.trans ?_ (LocalGradedHom.app_mk_congr (f U).toLocalGradedHom i i hij
    (Category.id_comp V.hom) x)
  exact (LocalHom.app_congr (hf (U := U) (U' := V.left) V.hom) i i (add_zero i)
    (Over.mk (𝟙 V.left)) x).symm

/-- A morphism of right differential graded modules is determined by the local homomorphisms it
restricts to. -/
theorem hom_ext_ofHom {ψ χ : K ⟶ L} (h : ∀ U : C, LocalHom.ofHom ψ U = LocalHom.ofHom χ U) :
    ψ = χ := by
  refine DifferentialGradedModule.Hom.ext fun k =>
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  have hx := LocalHom.app_congr (h U.unop) k k (add_zero k) (Over.mk (𝟙 U.unop)) x
  rwa [LocalHom.ofHom_app, LocalHom.ofHom_app, castHom_self, castHom_self] at hx

end DifferentialGradedModule

end Assemble

/-! ### The local tensor-hom identification -/

section LocalEquiv

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {M H : DifferentialGradedModule.{t, a, w} A}
  {N : DifferentialGradedBimodule.{t, a, z} A B} {L T : DifferentialGradedModule.{t, a, s} B}

/-- The degree-`n` local homomorphisms `(M ⊗_A N)|_U → L|_U` of right differential graded
`B`-modules are the degree-`n` local homomorphisms `M|_U → SheafHom^dg_B(N, L)|_U` of right
differential graded `A`-modules: both are the `A`-balanced bilinear families of degree `n`
over `U`. -/
noncomputable def tensorHomLocalEquiv (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (n : ℤ) (U : C) : LocalHom T L n U ≃ LocalHom M H n U :=
  (hT.universal L n U).trans (balancedEquivDg hH M n U).symm

/-- The local identification sends a local homomorphism `φ` out of the tensor product to the
local homomorphism `x ↦ (y ↦ φ (x ⊗ y))`. -/
theorem tensorHomLocalEquiv_eval (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (U : C) (f : LocalHom T L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) (j' k : ℤ) (hj'k : j' + j = k)
    (W : Over V.left) (y : (N.complex.X j').val.obj (Opposite.op W.left)) :
    (hH.isInternalHom.sectionsEquiv j V.left
        ((tensorHomLocalEquiv hT hH n U f).app i j hij V x)).app j' k hj'k W y =
      f.app (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
        (hT.tmul i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
          ((M.complex.X i).val.map W.hom.op x) y) :=
  (ofBalancedDg_sectionsEquiv_app hH (hT.universal L n U f) i j hij V x j' k hj'k W y).trans
    (hT.universal_app L n U f i j' k (by omega) (Over.mk (W.hom ≫ V.hom))
      ((M.complex.X i).val.map W.hom.op x) y)

/-- The local identification is compatible with restriction along a morphism of the site. -/
theorem tensorHomLocalEquiv_restrict (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (n : ℤ) {U U' : C} (g : U' ⟶ U) (f : LocalHom T L n U) :
    tensorHomLocalEquiv hT hH n U' (f.restrict g) =
      (tensorHomLocalEquiv hT hH n U f).restrict g := by
  have huniv : hT.universal L n U' (f.restrict g) = (hT.universal L n U f).restrict g :=
    LocalBalancedBilinear.ext fun i j k hijk V x y => by
      rw [LocalBalancedBilinear.restrict_app, hT.universal_restrict L n g f i j k hijk V x y]
  show ofBalancedDg hH (hT.universal L n U' (f.restrict g)) = _
  rw [huniv]
  exact (ofBalancedDg_restrict hH g (hT.universal L n U f)).symm

/-- The inverse of the local identification is compatible with restriction along a morphism of
the site. -/
theorem tensorHomLocalEquiv_symm_restrict (hT : IsTensorProduct M N T)
    (hH : IsSheafHom N L H) (n : ℤ) {U U' : C} (g : U' ⟶ U) (q : LocalHom M H n U) :
    (tensorHomLocalEquiv hT hH n U').symm (q.restrict g) =
      ((tensorHomLocalEquiv hT hH n U).symm q).restrict g :=
  (tensorHomLocalEquiv hT hH n U').injective (by
    rw [Equiv.apply_symm_apply, tensorHomLocalEquiv_restrict, Equiv.apply_symm_apply])

/-- The local identification carries the zero local homomorphism to the zero one. -/
theorem tensorHomLocalEquiv_zero (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (n : ℤ) (U : C) :
    tensorHomLocalEquiv hT hH n U (LocalHom.zero T L n U) = LocalHom.zero M H n U := by
  refine LocalHom.ext fun i j hij V x => hH.isInternalHom.sections_ext fun j' k hj'k W y => ?_
  rw [tensorHomLocalEquiv_eval hT hH n U _ i j hij V x j' k hj'k W y, LocalHom.zero_app,
    LocalHom.zero_app, hH.isInternalHom.sectionsEquiv_zero]

/-- The inverse of the local identification carries the zero local homomorphism to the zero
one. -/
theorem tensorHomLocalEquiv_symm_zero (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (n : ℤ) (U : C) :
    (tensorHomLocalEquiv hT hH n U).symm (LocalHom.zero M H n U) = LocalHom.zero T L n U :=
  (tensorHomLocalEquiv hT hH n U).symm_apply_eq.2 (tensorHomLocalEquiv_zero hT hH n U).symm

/-- A section of the internal hom reads a difference as the difference of the local
homomorphisms. -/
theorem IsInternalHom.sectionsEquiv_sub {A' : DifferentialGradedAlgebra.{t, a} R}
    {M' : DifferentialGradedModule.{t, a, w} A'} {L' : DifferentialGradedModule.{t, a, z} A'}
    {H' : CochainComplex (SheafOfModules.{s} R) ℤ} (hH' : IsInternalHom M' L' H') (n : ℤ)
    (U : C) (p q : (H'.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M'.complex.X i).val.obj (Opposite.op V.left)) :
    (hH'.sectionsEquiv n U (p - q)).app i j hij V x =
      (hH'.sectionsEquiv n U p).app i j hij V x - (hH'.sectionsEquiv n U q).app i j hij V x := by
  have h := hH'.sectionsEquiv_add n U (p - q) q i j hij V x
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- The differential of a degree-zero local homomorphism is the differential of the internal
hom, read on local sections. -/
theorem LocalHom.diff_app_eq_localDiffApp {A' : DifferentialGradedAlgebra.{t, a} R}
    {K' : DifferentialGradedModule.{t, a, w} A'} {L' : DifferentialGradedModule.{t, a, z} A'}
    {U : C} (f : LocalHom K' L' 0 U) (i j : ℤ) (hij : i + 1 = j) (V : Over U)
    (x : (K'.complex.X i).val.obj (Opposite.op V.left)) :
    f.diff.app i j hij V x = localDiffApp f.toLocalGradedHom 1 i j hij V x := by
  rw [localDiffApp_eq f.toLocalGradedHom 1 i j i (i + 1) hij (add_zero i) (by omega) V x,
    LocalHom.diff_app]
  obtain rfl : i + 1 = j := hij
  rw [Int.negOnePow_one]
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
  rw [sub_eq_add_neg]

/-- The local identification commutes with the differential of local homomorphisms: this is the
differential graded content of the tensor-hom adjunction. The hypothesis says that `f'` is the
differential of `f`. -/
theorem localDiffApp_tensorHomLocalEquiv (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (n m : ℤ) (U : C) (f : LocalHom T L n U) (f' : LocalHom T L m U)
    (hf' : ∀ (i j : ℤ) (hij : i + m = j) (V : Over U)
      (x : (T.complex.X i).val.obj (Opposite.op V.left)),
      f'.app i j hij V x = localDiffApp f.toLocalGradedHom m i j hij V x)
    (i j : ℤ) (hij : i + m = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (tensorHomLocalEquiv hT hH m U f').app i j hij V x =
      localDiffApp (tensorHomLocalEquiv hT hH n U f).toLocalGradedHom m i j hij V x := by
  refine hH.isInternalHom.sections_ext fun j' k hj'k W y => ?_
  have hlhs := (tensorHomLocalEquiv_eval hT hH m U f' i j hij V x j' k hj'k W y).trans
    (hf' (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
      (hT.tmul i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
        ((M.complex.X i).val.map W.hom.op x) y))
  rw [hlhs]
  by_cases hm : m = n + 1
  · subst hm
    have hdnat : (M.complex.X (i + 1)).val.map W.hom.op
          ((M.complex.d i (i + 1)).val.app (Opposite.op V.left) x) =
        (M.complex.d i (i + 1)).val.app (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
          ((M.complex.X i).val.map W.hom.op x) :=
      homSections_naturality (M.complex.d i (i + 1)) W.hom.op x
    rw [localDiffApp_eq f.toLocalGradedHom (n + 1) (i + j') k (i + j' + n) (i + j' + 1)
        (by omega) (by omega) (by omega) (Over.mk (W.hom ≫ V.hom)) _,
      hT.tmul_d_castHom i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
        ((M.complex.X i).val.map W.hom.op x) y,
      map_add, map_zsmul,
      LocalGradedHom.app_castHom_src f.toLocalGradedHom (add_right_comm i 1 j') (by omega)
        (Over.mk (W.hom ≫ V.hom)) _,
      LocalGradedHom.app_castHom_src f.toLocalGradedHom (add_assoc i j' 1).symm (by omega)
        (Over.mk (W.hom ≫ V.hom)) _,
      localDiffApp_eq (tensorHomLocalEquiv hT hH n U f).toLocalGradedHom (n + 1) i j (i + n)
        (i + 1) hij rfl (by omega) V x,
      hH.isInternalHom.sectionsEquiv_add j V.left _ _ j' k hj'k W y,
      hH.isInternalHom.sectionsEquiv_zsmul j V.left _ _ j' k hj'k W y,
      hH.isInternalHom.sectionsEquiv_d (i + n) j V.left
        ((tensorHomLocalEquiv hT hH n U f).app i (i + n) rfl V x) j' k hj'k W y,
      localDiffApp_eq (hH.isInternalHom.sectionsEquiv (i + n) V.left
          ((tensorHomLocalEquiv hT hH n U f).app i (i + n) rfl V x)).toLocalGradedHom
        j j' k (i + j' + n) (j' + 1) hj'k (by omega) (by omega) W y,
      tensorHomLocalEquiv_eval hT hH n U f i (i + n) rfl V x j' (i + j' + n) (by omega) W y,
      tensorHomLocalEquiv_eval hT hH n U f i (i + n) rfl V x (j' + 1) k (by omega) W
        ((N.toRightModule.complex.d j' (j' + 1)).val.app (Opposite.op W.left) y),
      tensorHomLocalEquiv_eval hT hH n U f (i + 1) j (by omega) V
        ((M.complex.d i (i + 1)).val.app (Opposite.op V.left) x) j' k (by omega) W y,
      hdnat]
    obtain rfl : j = i + n + 1 := by omega
    simp only [DifferentialGradedBimodule.toRightModule_complex, Over.mk_left]
    rw [smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add,
      show n + 1 + i = i + n + 1 by omega]
    abel
  · rw [localDiffApp_of_ne f.toLocalGradedHom m (i + j') k (by omega) hm
        (Over.mk (W.hom ≫ V.hom)) _,
      localDiffApp_of_ne (tensorHomLocalEquiv hT hH n U f).toLocalGradedHom m i j hij hm V x,
      hH.isInternalHom.sectionsEquiv_zero]

/-- The local identification carries the differential of a degree-zero local homomorphism to the
differential of its image. -/
theorem diff_tensorHomLocalEquiv (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (U : C)
    (f : LocalHom T L 0 U) :
    tensorHomLocalEquiv hT hH 1 U f.diff = (tensorHomLocalEquiv hT hH 0 U f).diff := by
  refine LocalHom.ext fun i j hij V x => ?_
  rw [LocalHom.diff_app_eq_localDiffApp]
  exact localDiffApp_tensorHomLocalEquiv hT hH 0 1 U f f.diff
    (fun i j hij V x => LocalHom.diff_app_eq_localDiffApp f i j hij V x) i j hij V x

end LocalEquiv

/-! ### The adjunction -/

section Adjunction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {M H : DifferentialGradedModule.{t, a, w} A}
  {N : DifferentialGradedBimodule.{t, a, z} A B} {L T : DifferentialGradedModule.{t, a, s} B}

/-- A degreewise morphism of graded sheaves of modules absorbs a transport of degrees. -/
theorem homSections_degreewise_castHom {X Y : ℤ → SheafOfModules.{s} R}
    (ψ : ∀ k : ℤ, X k ⟶ Y k) {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (x : (X i).val.obj U) :
    homSections (ψ j) U (castHom X h U x) = castHom Y h U (homSections (ψ i) U x) := by
  subst h
  rfl

/-- Restriction along the identity does not move a local section. -/
theorem map_id_sections (X : SheafOfModules.{s} R) (U : C) (x : X.val.obj (Opposite.op U)) :
    X.val.map (𝟙 U).op x = x := by
  rw [op_id, X.val.map_id]
  rfl

/-- Restriction along the identity object of a slice site does not move a local section. -/
theorem map_over_id_sections (X : SheafOfModules.{s} R) (U : C)
    (x : X.val.obj (Opposite.op U)) : X.val.map (Over.mk (𝟙 U)).hom.op x = x :=
  map_id_sections X U x

/-- The morphisms `M ⊗_A N ⟶ L` of right differential graded `B`-modules are the morphisms
`M ⟶ SheafHom^dg_B(N, L)` of right differential graded `A`-modules. -/
noncomputable def tensorHomEquivDg (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) :
    (T ⟶ L) ≃ (M ⟶ H) where
  toFun ψ := DifferentialGradedModule.homOfLocal
    (f := fun U => tensorHomLocalEquiv hT hH 0 U (LocalHom.ofHom ψ U))
    (fun g => by rw [← tensorHomLocalEquiv_restrict, LocalHom.restrict_ofHom])
    (fun U => by
      rw [← diff_tensorHomLocalEquiv, LocalHom.diff_ofHom, tensorHomLocalEquiv_zero])
  invFun φ := DifferentialGradedModule.homOfLocal
    (f := fun U => (tensorHomLocalEquiv hT hH 0 U).symm (LocalHom.ofHom φ U))
    (fun g => by rw [← tensorHomLocalEquiv_symm_restrict, LocalHom.restrict_ofHom])
    (fun U => by
      have h := diff_tensorHomLocalEquiv hT hH U
        ((tensorHomLocalEquiv hT hH 0 U).symm (LocalHom.ofHom φ U))
      rw [Equiv.apply_symm_apply, LocalHom.diff_ofHom] at h
      rw [← tensorHomLocalEquiv_symm_zero hT hH 1 U, ← h, Equiv.symm_apply_apply])
  left_inv ψ := DifferentialGradedModule.hom_ext_ofHom fun U => by
    rw [DifferentialGradedModule.ofHom_homOfLocal, DifferentialGradedModule.ofHom_homOfLocal,
      Equiv.symm_apply_apply]
  right_inv φ := DifferentialGradedModule.hom_ext_ofHom fun U => by
    rw [DifferentialGradedModule.ofHom_homOfLocal, DifferentialGradedModule.ofHom_homOfLocal,
      Equiv.apply_symm_apply]

/-- The bijection on morphisms sends `φ` to `x ↦ (y ↦ φ (x ⊗ y))`. -/
theorem tensorHomEquivDg_eval (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (ψ : T ⟶ L)
    (i j' k : ℤ) (hj'k : j' + i = k) (U : C) (x : (M.complex.X i).val.obj (Opposite.op U))
    (W : Over U) (y : (N.complex.X j').val.obj (Opposite.op W.left)) :
    (hH.isInternalHom.sectionsEquiv i U
        (((tensorHomEquivDg hT hH ψ).toHomologicalComplex.f i).val.app
          (Opposite.op U) x)).app j' k hj'k W y =
      castHom L.complex.X (show i + j' = k by omega) (Opposite.op W.left)
        ((ψ.toHomologicalComplex.f (i + j')).val.app (Opposite.op W.left)
          (hT.tmul i j' (Opposite.op W.left) ((M.complex.X i).val.map W.hom.op x) y)) := by
  refine Eq.trans (tensorHomLocalEquiv_eval hT hH 0 U (LocalHom.ofHom ψ U) i i (add_zero i)
    (Over.mk (𝟙 U)) x j' k hj'k W y) ?_
  rw [LocalHom.ofHom_app]
  rfl

/-- The inverse bijection on morphisms, evaluated on a local section of the tensor product. -/
theorem tensorHomEquivDg_symm_eval (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (φ : M ⟶ H) (i j' k : ℤ) (hj'k : j' + i = k) (U : C)
    (x : (M.complex.X i).val.obj (Opposite.op U)) (W : Over U)
    (y : (N.complex.X j').val.obj (Opposite.op W.left)) :
    castHom L.complex.X (show i + j' = k by omega) (Opposite.op W.left)
        ((((tensorHomEquivDg hT hH).symm φ).toHomologicalComplex.f (i + j')).val.app
          (Opposite.op W.left)
          (hT.tmul i j' (Opposite.op W.left) ((M.complex.X i).val.map W.hom.op x) y)) =
      (hH.isInternalHom.sectionsEquiv i U
        ((φ.toHomologicalComplex.f i).val.app (Opposite.op U) x)).app j' k hj'k W y := by
  have h := tensorHomEquivDg_eval hT hH ((tensorHomEquivDg hT hH).symm φ) i j' k hj'k U x W y
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The bijection on morphisms, evaluated over the object of the site itself. -/
theorem tensorHomEquivDg_eval_top (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (ψ : T ⟶ L) (i j' k : ℤ) (hj'k : j' + i = k) (U : C)
    (x : (M.complex.X i).val.obj (Opposite.op U))
    (y : (N.complex.X j').val.obj (Opposite.op U)) :
    (hH.isInternalHom.sectionsEquiv i U
        (((tensorHomEquivDg hT hH ψ).toHomologicalComplex.f i).val.app
          (Opposite.op U) x)).app j' k hj'k (Over.mk (𝟙 U)) y =
      castHom L.complex.X (show i + j' = k by omega) (Opposite.op U)
        ((ψ.toHomologicalComplex.f (i + j')).val.app (Opposite.op U)
          (hT.tmul i j' (Opposite.op U) x y)) := by
  refine Eq.trans (tensorHomEquivDg_eval hT hH ψ i j' k hj'k U x (Over.mk (𝟙 U)) y) ?_
  rw [map_over_id_sections]
  rfl

/-- The inverse bijection on morphisms, evaluated over the object of the site itself. -/
theorem tensorHomEquivDg_symm_eval_top (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (φ : M ⟶ H) (i j' : ℤ) (U : C) (x : (M.complex.X i).val.obj (Opposite.op U))
    (y : (N.complex.X j').val.obj (Opposite.op U)) :
    ((((tensorHomEquivDg hT hH).symm φ).toHomologicalComplex.f (i + j')).val.app
        (Opposite.op U) (hT.tmul i j' (Opposite.op U) x y)) =
      (hH.isInternalHom.sectionsEquiv i U
        ((φ.toHomologicalComplex.f i).val.app (Opposite.op U) x)).app j' (i + j')
          (by omega) (Over.mk (𝟙 U)) y := by
  refine Eq.trans ?_ (tensorHomEquivDg_symm_eval hT hH φ i j' (i + j') (by omega) U x
    (Over.mk (𝟙 U)) y)
  rw [map_over_id_sections]
  rfl

/-- Two morphisms out of a tensor product which agree on the image of the multiplication map
are equal. -/
theorem IsTensorProduct.hom_ext_tmul (hT : IsTensorProduct M N T) {ψ χ : T ⟶ L}
    (h : ∀ (i j : ℤ) (U : C) (x : (M.complex.X i).val.obj (Opposite.op U))
      (y : (N.complex.X j).val.obj (Opposite.op U)),
      (ψ.toHomologicalComplex.f (i + j)).val.app (Opposite.op U)
          (hT.tmul i j (Opposite.op U) x y) =
        (χ.toHomologicalComplex.f (i + j)).val.app (Opposite.op U)
          (hT.tmul i j (Opposite.op U) x y)) : ψ = χ :=
  DifferentialGradedModule.hom_ext_ofHom fun U =>
    hT.localHom_ext fun i j k hijk V x y => by
      rw [LocalHom.ofHom_app, LocalHom.ofHom_app]
      exact congrArg _ (h i j V.left x y)

/-- **The tensor-hom adjunction for sheaves of differential graded modules**: a tensor product
functor `- ⊗_A N` is left adjoint to an internal hom functor `SheafHom^dg_B(N, -)`, by the
bijection `φ ↦ (x ↦ (y ↦ φ (x ⊗ y)))` on local sections. -/
noncomputable def tensorSheafHomAdjunction (D : TensorFunctorData.{t, a, w, z, s} A B N)
    (S : SheafHomFunctorData.{t, a, w, s, z} N) : D.functor ⊣ S.functor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M' L' => tensorHomEquivDg (D.isTensorProduct M') (S.isSheafHom L')
      homEquiv_naturality_left_symm := fun {X' X Y} f g =>
        (D.isTensorProduct X').hom_ext_tmul fun i j U x y => by
          have e1 := tensorHomEquivDg_symm_eval_top (D.isTensorProduct X') (S.isSheafHom Y)
            (f ≫ g) i j U x y
          have e2 := tensorHomEquivDg_symm_eval_top (D.isTensorProduct X) (S.isSheafHom Y) g
            i j U ((f.toHomologicalComplex.f i).val.app (Opposite.op U) x) y
          have e3 := congrArg
            (fun q => (((tensorHomEquivDg (D.isTensorProduct X)
                (S.isSheafHom Y)).symm g).toHomologicalComplex.f (i + j)).val.app
              (Opposite.op U) q)
            (D.map_spec f i j (Opposite.op U) x y)
          exact e1.trans (e3.trans e2).symm
      homEquiv_naturality_right := fun {X Y Y'} f g =>
        DifferentialGradedModule.hom_ext_ofHom fun U =>
          LocalHom.ext fun i j hij V x => by
            obtain rfl : i = j := by omega
            rw [LocalHom.ofHom_app, LocalHom.ofHom_app, castHom_self, castHom_self]
            refine (S.isSheafHom Y').isInternalHom.sections_ext fun j' k hj'k W y => ?_
            have e1 := tensorHomEquivDg_eval (D.isTensorProduct X) (S.isSheafHom Y') (f ≫ g)
              i j' k hj'k V.left x W y
            have e3 := tensorHomEquivDg_eval (D.isTensorProduct X) (S.isSheafHom Y) f
              i j' k hj'k V.left x W y
            have e2 := S.map_spec g i V.left
              (((tensorHomEquivDg (D.isTensorProduct X)
                (S.isSheafHom Y) f).toHomologicalComplex.f i).val.app (Opposite.op V.left) x)
              j' k hj'k W y
            rw [e3] at e2
            have e4 := homSections_degreewise_castHom (fun q => g.toHomologicalComplex.f q)
              (show i + j' = k by omega) (Opposite.op W.left)
              ((f.toHomologicalComplex.f (i + j')).val.app (Opposite.op W.left)
                ((D.isTensorProduct X).tmul i j' (Opposite.op W.left)
                  ((X.complex.X i).val.map W.hom.op x) y))
            exact e1.trans (e4.symm.trans e2.symm) }

end Adjunction

end SheafOfModules

end
