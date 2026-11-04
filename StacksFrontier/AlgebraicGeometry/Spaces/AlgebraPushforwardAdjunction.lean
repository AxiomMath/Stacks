module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism

/-!
# Direct image of algebra sheaves along a morphism of algebraic spaces

Let `g : Y ⟶ X` be a morphism of algebraic spaces.  The direct image `g_* 𝒞` of a sheaf `𝒞` of
commutative `𝒪_Y`-algebras on the small étale site of `Y` is a sheaf of commutative
`𝒪_X`-algebras, through `𝒪_X ⟶ g_* 𝒪_Y ⟶ g_* 𝒞`.  This file constructs that functor, shows that
the pullback of algebra sheaves `AlgebraicGeometry.Space.algebraPullback` is left adjoint to it,
and identifies the direct image of a direct-image algebra with the direct-image algebra of the
composite.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.homMk` is a morphism of sheaves of rings commuting with
  the structure maps, as a morphism of algebra sheaves.
* `AlgebraicGeometry.Space.algebraPushforward` is the direct image functor on algebra sheaves.
* `AlgebraicGeometry.Space.algebraPullbackPushforwardAdjunction` is the adjunction
  `g^* ⊣ g_*` on algebra sheaves.
* `AlgebraicGeometry.Space.algebraPushforwardPushforwardAlgebraIso` is the isomorphism
  `g_* (W_* 𝒪_W) ≅ (W ≫ g)_* 𝒪_W` of `𝒪_X`-algebras, for `W` an algebraic space over `Y`.
* `AlgebraicGeometry.Space.pushforwardAlgebraCompHomEquiv` is the resulting bijection between
  algebra maps `𝒜 ⟶ (W ≫ g)_* 𝒪_W` and algebra maps `g^* 𝒜 ⟶ W_* 𝒪_W`.

## Implementation notes

The adjunction is assembled from the adjunction between inverse image and direct image of
sheaves of commutative rings, `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, and the
universal property of the pushout defining `AlgebraicGeometry.Space.algebraPullback`: a map of
`𝒪_Y`-algebras out of `𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹𝒜` is a map of rings out of `g⁻¹𝒜` which restricts on
`g⁻¹𝒪_X` to the structure map, and transposing it gives a map of rings `𝒜 ⟶ g_* 𝒞` which
restricts on `𝒪_X` to the structure map of `g_* 𝒞`, because the inverse-image structure map
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is by definition the transpose of `g♯`.

The identification of the direct image of a direct-image algebra is the composition law of
Stacks 03G8, `AlgebraicGeometry.Space.fSharp_comp_compRingIso`, which is exactly the statement
that the comparison of iterated direct images carries structure map to structure map.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- A morphism of the underlying sheaves of rings which carries the structure map of the source
to the structure map of the target, as a morphism of algebra sheaves.  The converse is
`AlgebraicGeometry.Space.AlgebraSheaf.hom_comp_right`. -/
def homMk {A C : AlgebraSheaf.{u, u} B S hS F hF} (ρ : A.right ⟶ C.right)
    (h : A.hom ≫ ρ = C.hom) : A ⟶ C where
  right := ρ
  comm U r := ConcreteCategory.congr_hom (commRingSheafHom_app_congr h U) r

/-- The underlying morphism of sheaves of rings of `homMk ρ h` is `ρ`. -/
@[simp]
theorem homMk_right {A C : AlgebraSheaf.{u, u} B S hS F hF} (ρ : A.right ⟶ C.right)
    (h : A.hom ≫ ρ = C.hom) : (homMk ρ h).right = ρ :=
  rfl

end AlgebraSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The direct image functor -/

/-- The direct image `g_* 𝒞` of a sheaf of `𝒪_Y`-algebras along `g : Y ⟶ X`, as a sheaf of
`𝒪_X`-algebras through `g♯ : 𝒪_X ⟶ g_* 𝒪_Y`. -/
def algebraPushforward (g : Y ⟶ X) :
    AlgebraSheaf.{u, u} B S hS Y.1 Y.2 ⥤ AlgebraSheaf.{u, u} B S hS X.1 X.2 where
  obj C := AlgebraSheaf.ofHom ((smallEtaleRingedToposHom B S hS g).fSharp ≫
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map C.hom)
  map {C D} φ := AlgebraSheaf.ofHomMap
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map φ.right)
    (by rw [Category.assoc, ← Functor.map_comp, AlgebraSheaf.hom_comp_right φ])
  map_id C := AlgebraSheaf.Hom.ext
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map_id
      C.right)
  map_comp φ ψ := AlgebraSheaf.Hom.ext
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map_comp
      φ.right ψ.right)

/-- The underlying sheaf of rings of `g_* 𝒞` is the direct image of that of `𝒞`. -/
@[simp]
theorem algebraPushforward_obj_right (g : Y ⟶ X) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    ((algebraPushforward B S hS g).obj C).right =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        C.right :=
  rfl

/-- The structure map of `g_* 𝒞` is `g♯` followed by the direct image of the structure map
of `𝒞`. -/
@[simp]
theorem algebraPushforward_obj_hom (g : Y ⟶ X) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    ((algebraPushforward B S hS g).obj C).hom =
      (smallEtaleRingedToposHom B S hS g).fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
          C.hom :=
  rfl

/-- The underlying morphism of sheaves of rings of `g_* φ` is the direct image of that of
`φ`. -/
@[simp]
theorem algebraPushforward_map_right (g : Y ⟶ X) {C D : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    (φ : C ⟶ D) :
    ((algebraPushforward B S hS g).map φ).right =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
        φ.right :=
  rfl

/-! ### The adjunction -/

section Adjunction

variable {B S hS}

/-- The ring-level transpose of `g♯`, followed by the structure map of `𝒞`, is the transpose of
the structure map of `g_* 𝒞`. -/
theorem commRingImageAdjunction_homEquiv_structure (g : Y ⟶ X)
    (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    (commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _
        (structurePullbackMap B S hS g ≫ C.hom) =
      ((algebraPushforward B S hS g).obj C).hom :=
  ((commRingImageAdjunction
      (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv_naturality_right
      (structurePullbackMap B S hS g) C.hom).trans
    (congrArg (· ≫ (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS g).toToposHom).map C.hom)
      (Equiv.apply_symm_apply _ _))

/-- A morphism `g^* 𝒜 ⟶ 𝒞` of algebra sheaves, restricted to `g⁻¹𝒜`, restricts further on
`g⁻¹𝒪_X` to the inverse-image structure map followed by the structure map of `𝒞`. -/
theorem ringSheafPullback_map_hom_comp_algebraPullbackMap (g : Y ⟶ X)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} {C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    (φ : (algebraPullback B S hS g).obj A ⟶ C) :
    (ringSheafPullback B S hS g).map A.hom ≫ (algebraPullbackMap B S hS g).app A ≫ φ.right =
      structurePullbackMap B S hS g ≫ C.hom :=
  ((algebraPullback_isPushout B S hS g A).w_assoc φ.right).trans
    (congrArg (structurePullbackMap B S hS g ≫ ·) (AlgebraSheaf.hom_comp_right φ))

/-- The forward direction of the adjunction: transpose the restriction of `φ` to `g⁻¹𝒜`. -/
def algebraPullbackHomEquivToFun (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (φ : (algebraPullback B S hS g).obj A ⟶ C) :
    A ⟶ (algebraPushforward B S hS g).obj C :=
  AlgebraSheaf.homMk
    ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _
      ((algebraPullbackMap B S hS g).app A ≫ φ.right))
    (((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv_naturality_left
          A.hom ((algebraPullbackMap B S hS g).app A ≫ φ.right)).symm.trans
      ((congrArg ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
          (ringSheafPullback_map_hom_comp_algebraPullbackMap g φ)).trans
        (commRingImageAdjunction_homEquiv_structure g C)))

/-- The transpose of a morphism `𝒜 ⟶ g_* 𝒞` of algebra sheaves, restricted on `g⁻¹𝒪_X`, is the
inverse-image structure map followed by the structure map of `𝒞`. -/
theorem ringSheafPullback_map_hom_comp_homEquiv_symm (g : Y ⟶ X)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} {C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    (ψ : A ⟶ (algebraPushforward B S hS g).obj C) :
    (ringSheafPullback B S hS g).map A.hom ≫
        ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
          A.right C.right).symm ψ.right =
      structurePullbackMap B S hS g ≫ C.hom :=
  ((commRingImageAdjunction
      (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv_naturality_left_symm
        A.hom ψ.right).symm.trans
    ((congrArg ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _).symm
      ((AlgebraSheaf.hom_comp_right ψ).trans
        (commRingImageAdjunction_homEquiv_structure g C).symm)).trans
      (Equiv.symm_apply_apply _ _))

/-- The inverse direction of the adjunction: the pushout map out of `𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹𝒜`
given by the transpose of `ψ` and the structure map of `𝒞`. -/
def algebraPullbackHomEquivInvFun (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (ψ : A ⟶ (algebraPushforward B S hS g).obj C) :
    (algebraPullback B S hS g).obj A ⟶ C :=
  AlgebraSheaf.homMk
    ((algebraPullback_isPushout B S hS g A).desc
      (((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        A.right C.right).symm ψ.right) C.hom
      (ringSheafPullback_map_hom_comp_homEquiv_symm g ψ))
    ((algebraPullback_isPushout B S hS g A).inr_desc _ _ _)

/-- **Pullback of algebra sheaves is left adjoint to direct image**: algebra maps
`g^* 𝒜 ⟶ 𝒞` correspond to algebra maps `𝒜 ⟶ g_* 𝒞`. -/
def algebraPullbackHomEquiv (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    ((algebraPullback B S hS g).obj A ⟶ C) ≃ (A ⟶ (algebraPushforward B S hS g).obj C) where
  toFun := algebraPullbackHomEquivToFun g A C
  invFun := algebraPullbackHomEquivInvFun g A C
  left_inv φ := AlgebraSheaf.Hom.ext ((algebraPullback_isPushout B S hS g A).hom_ext
    (((algebraPullback_isPushout B S hS g A).inl_desc _ _ _).trans (Equiv.symm_apply_apply _ _))
    (((algebraPullback_isPushout B S hS g A).inr_desc _ _ _).trans
      (AlgebraSheaf.hom_comp_right φ).symm))
  right_inv _ := AlgebraSheaf.Hom.ext
    ((congrArg ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        A.right C.right) ((algebraPullback_isPushout B S hS g A).inl_desc _ _ _)).trans
      (Equiv.apply_symm_apply _ _))

/-- The adjunction bijection on underlying sheaves of rings: the ring-level transpose of the
restriction to `g⁻¹𝒜`. -/
theorem algebraPullbackHomEquiv_apply_right (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (φ : (algebraPullback B S hS g).obj A ⟶ C) :
    (algebraPullbackHomEquiv g A C φ).right =
      (commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _
        ((algebraPullbackMap B S hS g).app A ≫ φ.right) :=
  rfl

/-- The inverse of the adjunction bijection, restricted to `g⁻¹𝒜`, is the ring-level inverse
transpose. -/
theorem algebraPullbackMap_app_comp_algebraPullbackHomEquiv_symm_right (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (ψ : A ⟶ (algebraPushforward B S hS g).obj C) :
    (algebraPullbackMap B S hS g).app A ≫ ((algebraPullbackHomEquiv g A C).symm ψ).right =
      ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        A.right C.right).symm ψ.right :=
  (algebraPullback_isPushout B S hS g A).inl_desc _ _ _

/-- The inverse of the adjunction bijection is natural in the algebra on `X`, on the restriction
to the inverse image `g⁻¹𝒜`. -/
theorem algebraPullbackMap_app_comp_algebraPullbackHomEquiv_symm_comp (g : Y ⟶ X)
    {A A' : AlgebraSheaf.{u, u} B S hS X.1 X.2} {C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    (f : A ⟶ A') (ψ : A' ⟶ (algebraPushforward B S hS g).obj C) :
    (algebraPullbackMap B S hS g).app A ≫ ((algebraPullbackHomEquiv g A C).symm (f ≫ ψ)).right =
      (algebraPullbackMap B S hS g).app A ≫
        ((algebraPullback B S hS g).map f ≫ (algebraPullbackHomEquiv g A' C).symm ψ).right := by
  have hn : (algebraPullbackMap B S hS g).app A ≫ ((algebraPullback B S hS g).map f).right =
      (ringSheafPullback B S hS g).map f.right ≫ (algebraPullbackMap B S hS g).app A' :=
    ((algebraPullbackMap B S hS g).naturality f).symm
  have h1 := algebraPullbackMap_app_comp_algebraPullbackHomEquiv_symm_right g A C (f ≫ ψ)
  have h2 := algebraPullbackMap_app_comp_algebraPullbackHomEquiv_symm_right g A' C ψ
  have h3 := (commRingImageAdjunction
    (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv_naturality_left_symm f.right ψ.right
  exact (h1.trans h3).trans
    (((congrArg (fun k => (ringSheafPullback B S hS g).map f.right ≫ k) h2).symm.trans
      (Category.assoc _ _ _).symm).trans
      ((congrArg (· ≫ ((algebraPullbackHomEquiv g A' C).symm ψ).right) hn.symm).trans
        (Category.assoc _ _ _)))

variable (B S hS) in
/-- **Pullback of algebra sheaves is left adjoint to direct image**, as functors: the
pullback `g^*` of algebra sheaves along a morphism `g : Y ⟶ X` of algebraic spaces is left
adjoint to the direct image `g_*`. -/
def algebraPullbackPushforwardAdjunction (g : Y ⟶ X) :
    algebraPullback B S hS g ⊣ algebraPushforward B S hS g :=
  Adjunction.mkOfHomEquiv
    { homEquiv := algebraPullbackHomEquiv g
      homEquiv_naturality_left_symm := fun {A A' C} f ψ =>
        AlgebraSheaf.Hom.ext ((algebraPullback_isPushout B S hS g A).hom_ext
          (algebraPullbackMap_app_comp_algebraPullbackHomEquiv_symm_comp g f ψ)
          ((AlgebraSheaf.hom_comp_right ((algebraPullbackHomEquiv g A C).symm (f ≫ ψ))).trans
            (AlgebraSheaf.hom_comp_right
              ((algebraPullback B S hS g).map f ≫ (algebraPullbackHomEquiv g A' C).symm ψ)).symm))
      homEquiv_naturality_right := fun _ _ =>
        AlgebraSheaf.Hom.ext
          ((congrArg ((commRingImageAdjunction
              (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
            (Category.assoc _ _ _).symm).trans
          ((commRingImageAdjunction
            (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv_naturality_right _ _)) }

end Adjunction

/-! ### The direct image of a direct-image algebra -/

/-- **The direct image of a direct-image algebra is the direct-image algebra of the composite**:
for `g : Y ⟶ X` and `W` an algebraic space over `Y`, `g_* (W_* 𝒪_W) ≅ (W ≫ g)_* 𝒪_W` as
`𝒪_X`-algebras.  On sheaves of rings this is the comparison of iterated direct images of
Stacks 03G8, and it respects the structure maps by the composition law
`AlgebraicGeometry.Space.fSharp_comp_compRingIso`. -/
def algebraPushforwardPushforwardAlgebraIso (g : Y ⟶ X) (W : Over Y) :
    (algebraPushforward B S hS g).obj (pushforwardAlgebra B S hS W) ≅
      pushforwardAlgebra B S hS (Over.mk (W.hom ≫ g)) :=
  let e := pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS W.hom).toToposHom
      (smallEtaleRingedToposHom B S hS g).toToposHom (smallEtaleRingedTopos B S hS W.left).O ≪≫
    (smallEtaleRingedToposHom_compRingIso B S hS W.hom g).app
      (smallEtaleRingedTopos B S hS W.left).O
  { hom := AlgebraSheaf.homMk e.hom (by
      have h := fSharp_comp_compRingIso B S hS W.hom g (𝟙 _)
      simp only [Category.comp_id] at h
      exact (Category.assoc _ _ _).trans h)
    inv := AlgebraSheaf.homMk e.inv (fSharp_comp_compRingIso_inv B S hS W.hom g)
    hom_inv_id := AlgebraSheaf.Hom.ext e.hom_inv_id
    inv_hom_id := AlgebraSheaf.Hom.ext e.inv_hom_id }

/-- **Algebra maps into the direct image along a composite are algebra maps out of the
pullback**: for `g : Y ⟶ X`, `W` an algebraic space over `Y` and `𝒜` a sheaf of
`𝒪_X`-algebras, maps `𝒜 ⟶ (W ≫ g)_* 𝒪_W` correspond to maps `g^* 𝒜 ⟶ W_* 𝒪_W`.  This is the
transpose by which the points of a relative spectrum over `X` lying over a chart `Y` are read
as points of the relative spectrum over `Y` of the pullback. -/
def pushforwardAlgebraCompHomEquiv (g : Y ⟶ X) (W : Over Y)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (A ⟶ pushforwardAlgebra B S hS (Over.mk (W.hom ≫ g))) ≃
      ((algebraPullback B S hS g).obj A ⟶ pushforwardAlgebra B S hS W) :=
  ((algebraPushforwardPushforwardAlgebraIso B S hS g W).homToEquiv).symm.trans
    (algebraPullbackHomEquiv g A (pushforwardAlgebra B S hS W)).symm

end AlgebraicGeometry.Space

end
