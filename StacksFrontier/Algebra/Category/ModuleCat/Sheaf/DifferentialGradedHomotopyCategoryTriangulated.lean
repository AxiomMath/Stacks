module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomC
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryProducts
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomotopyCategoryTriangulated

/-!
# The homotopy category of sheaf differential graded modules is triangulated

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. The
homotopy category `K(A)` of right differential graded `A`-modules is the homotopy category of
the differential graded category of those modules, and that differential graded category
satisfies axioms (A), (B) and (C). Hence `K(A)` is a triangulated category, with the shifts of
the differential graded shift functors and with the triangles of admissible short exact
sequences as its distinguished triangles.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyCategoryEquivalence`: the identification of
  `K(A)` with the homotopy category of the differential graded category of right differential
  graded `A`-modules.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.instHasShift`: the translation
  functors of `K(A)`, transported from the differential graded shifts.

## Main results

* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.instIsTriangulated`: `K(A)` is a
  triangulated category.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj`: the degree-one
  translation of `K(A)` is the shift of differential graded modules.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.distinguished_iff`: a triangle of
  `K(A)` is distinguished exactly when it is isomorphic to the triangle of an admissible short
  exact sequence of right differential graded modules.

## Implementation notes

The equivalence is built as in the non-sheaf case: a morphism of differential graded modules is
the same thing as a closed degree-zero homogeneous map, homotopies correspond to degree `-1`
homogeneous maps with the same coboundary, and both correspondences are bijective, so the
induced functor on homotopy categories is fully faithful and essentially surjective. Because
the objects and homogeneous morphisms of the differential graded category are identified with
differential graded modules and action-linear cochains only up to an equality of types, the
correspondences are stated through those transports.

The structures on `K(A)` are then transported along the equivalence. The preadditive structure
and the zero object are the ones already fixed for `K(A)`, and additivity of the equivalence is
deduced from the fact that it preserves binary products and zero morphisms rather than from a
formula for the sum of two homotopy classes. The translation functors are lifted with
`CategoryTheory.Functor.FullyFaithful.hasShift`, so that the equivalence commutes with the
shifts by construction and the degree-one translation of a differential graded module is the
shift of Stacks 0FS5.

The cone situation is obtained by choice, because Stacks 0FS6 asserts only that one exists;
this follows the precedent of
`SheafOfModules.DifferentialGradedModule.dgCategoryData` and of
`SheafOfModules.DifferentialGradedModule.shiftPackage`. Every structure here is otherwise a
genuine term built from that datum, so strengthening 0FS6 to return the cone situation instead
of asserting its existence would remove the last choice of data in this chain.

### No `@[stacks 0FSQ]`

Stacks 0FSQ is the assertion that, for a graded injective differential graded module `I` and a
short exact sequence `0 → M₁ → M₂ → M₃ → 0` of differential graded modules that is *not* assumed
admissible, applying `Hom` into `I` gives a short exact sequence of complexes of
`Γ(C, O)`-modules whose long exact cohomology sequence is a six-term cyclic exact sequence of
the groups `Hom` into `I` in the homotopy category and their shifts. What is here is the
triangulated structure that makes those groups and their shifts available: the shifts, the
distinguished triangles and the octahedron axiom. Both displays of the remark — the exactness
of the Hom-complex sequence, which is where graded injectivity enters and which does not come
from a distinguished triangle because the sequence is not admissible, and the resulting long
exact sequence of the groups of homomorphisms into the translates of `I` — are proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjectiveHomSequence`, where
they carry the bare attribute; the translation functors through which the terms of that
sequence are read are the `dgHomotopyHasShift` of this file, so no `@[stacks 0FSQ]` attribute
is placed here.

## References

* [Stacks Project, Tag 0FRZ](https://stacks.math.columbia.edu/tag/0FRZ)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 0FSQ](https://stacks.math.columbia.edu/tag/0FSQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

universe u v w

namespace CategoryTheory

universe u₁ u₂ v₁ v₂

variable {B : Type u₁} {E : Type u₂} [Category.{v₁} B] [Category.{v₂} E]

/-- The endofunctor of `B` obtained from an endofunctor `S` of `E` by a fully faithful functor
`F : B ⥤ E` whose image contains the objects of `E` up to equality. -/
def Functor.FullyFaithful.liftEndofunctor {F : B ⥤ E} (hF : F.FullyFaithful) (r : E → B)
    (hr : ∀ Y, F.obj (r Y) = Y) (S : E ⥤ E) : B ⥤ B where
  obj M := r (S.obj (F.obj M))
  map {M N} f := hF.preimage (eqToHom (hr _) ≫ S.map (F.map f) ≫ eqToHom (hr _).symm)
  map_id M := hF.map_injective (by simp)
  map_comp f g := hF.map_injective (by simp)

/-- The lifted endofunctor is intertwined with the original one by the fully faithful functor. -/
def Functor.FullyFaithful.liftEndofunctorIso {F : B ⥤ E} (hF : F.FullyFaithful) (r : E → B)
    (hr : ∀ Y, F.obj (r Y) = Y) (S : E ⥤ E) :
    hF.liftEndofunctor r hr S ⋙ F ≅ F ⋙ S :=
  NatIso.ofComponents (fun M => eqToIso (hr _)) (by
    intro M N f
    simp [Functor.FullyFaithful.liftEndofunctor])

/-- The lift of an additive endofunctor along an additive fully faithful functor is additive. -/
theorem Functor.FullyFaithful.liftEndofunctor_additive [Preadditive B] [Preadditive E]
    {F : B ⥤ E} [F.Additive] (hF : F.FullyFaithful) (r : E → B)
    (hr : ∀ Y, F.obj (r Y) = Y) (S : E ⥤ E) [S.Additive] :
    (hF.liftEndofunctor r hr S).Additive := by
  have : F.Faithful := hF.faithful
  have : (hF.liftEndofunctor r hr S ⋙ F).Additive :=
    Functor.additive_of_iso (hF.liftEndofunctorIso r hr S).symm
  exact Functor.additive_of_comp_faithful _ F

/-- Composing with the inverse of a natural isomorphism and then with the isomorphism itself
leaves a morphism unchanged. -/
private theorem comp_inv_hom_app {F G : B ⥤ E} (α : F ≅ G) (Y : B) {Z : E}
    (f : Z ⟶ G.obj Y) : (f ≫ α.inv.app Y) ≫ α.hom.app Y = f := by
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

open CategoryTheory.Limits CategoryTheory.Pretriangulated in
/-- A category equivalent to a pretriangulated category, by an additive equivalence commuting
with the shifts, is pretriangulated with the triangles whose image is distinguished. -/
@[instance_reducible]
noncomputable def Pretriangulated.ofEquivalence
    [HasZeroObject B] [HasZeroObject E] [Preadditive B] [Preadditive E]
    [HasShift B ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] (F : B ⥤ E) [F.IsEquivalence] [F.Additive] [F.CommShift ℤ] :
    Pretriangulated B where
  distinguishedTriangles := {T | F.mapTriangle.obj T ∈ distTriang E}
  isomorphic_distinguished T hT U e :=
    Pretriangulated.isomorphic_distinguished _ hT _ (F.mapTriangle.mapIso e)
  contractible_distinguished M := by
    apply (distinguished_iff_of_iso (Triangle.isoMk
      (F.mapTriangle.obj (contractibleTriangle M)) (contractibleTriangle (F.obj M))
      (Iso.refl _) (Iso.refl _) ((F.map_isZero (isZero_zero B)).isoZero)
      (by simp [Functor.mapTriangle, contractibleTriangle])
      (by simp [Functor.mapTriangle, contractibleTriangle])
      (by simp [Functor.mapTriangle, contractibleTriangle]))).2
    exact Pretriangulated.contractible_distinguished _
  distinguished_cocone_triangle {M N} f := by
    obtain ⟨Z, g, h, ht⟩ := Pretriangulated.distinguished_cocone_triangle (F.map f)
    let Z' := F.objPreimage Z
    let e : F.obj Z' ≅ Z := F.objObjPreimageIso Z
    let g' : N ⟶ Z' := F.preimage (g ≫ e.inv)
    let h' : Z' ⟶ (shiftFunctor B (1 : ℤ)).obj M :=
      F.preimage (e.hom ≫ h ≫ (F.commShiftIso (1 : ℤ)).inv.app M)
    refine ⟨Z', g', h', ?_⟩
    apply (distinguished_iff_of_iso (Triangle.isoMk
      (F.mapTriangle.obj (Triangle.mk f g' h')) (Triangle.mk (F.map f) g h)
      (Iso.refl _) (Iso.refl _) e (by simp [Functor.mapTriangle])
      (by simp [Functor.mapTriangle, g'])
      (by simp [Functor.mapTriangle, h']))).2 ht
  rotate_distinguished_triangle T :=
    (Pretriangulated.rotate_distinguished_triangle (F.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (F.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T U hT hU a b hab := by
    obtain ⟨c, hc₁, hc₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism
      (F.mapTriangle.obj T) (F.mapTriangle.obj U) hT hU (F.map a) (F.map b)
      (by simpa only [Functor.mapTriangle, Triangle.mk, Functor.map_comp] using congrArg F.map hab)
    let φ := Triangle.homMk (F.mapTriangle.obj T) (F.mapTriangle.obj U)
      (F.map a) (F.map b) c
      (by simpa only [Functor.mapTriangle, Triangle.mk, Functor.map_comp] using congrArg F.map hab)
      hc₁ hc₂
    let ψ := F.mapTriangle.preimage φ
    have ha : ψ.hom₁ = a := F.map_injective (by
      change (F.mapTriangle.map ψ).hom₁ = _
      rw [Functor.map_preimage]
      rfl)
    have hb : ψ.hom₂ = b := F.map_injective (by
      change (F.mapTriangle.map ψ).hom₂ = _
      rw [Functor.map_preimage]
      rfl)
    exact ⟨ψ.hom₃, by simpa only [ha, hb] using ψ.comm₂,
      by simpa only [ha, hb] using ψ.comm₃⟩

end CategoryTheory

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-! ### Morphisms of differential graded modules as closed degree-zero homogeneous maps -/

/-- The cochain of the differential of a homogeneous morphism is the Hom-complex commutator. -/
private theorem bridgeUnderlying_d (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : D.category.Hom (D.objects.symm ▸ M) (D.objects.symm ▸ N) n) :
    underlyingCochain A D (D.category.d f) = δ n (n + 1) (underlyingCochain A D f) :=
  eq_of_heq (D.differential M N n f)

/-- The commutator formula for the differential of a morphism of degree `-1`. -/
private theorem bridgeUnderlying_d' (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (f : D.category.Hom (D.objects.symm ▸ M) (D.objects.symm ▸ N) (-1)) :
    underlyingCochain A D (D.category.d' (show (-1 : ℤ) + 1 = 0 by omega) f) =
      δ (-1) 0 (underlyingCochain A D f) := by
  change (D.homs M N 0 ▸ D.category.d f).val = _
  rw [eq_of_heq (D.differential M N (-1) f)]
  change δ (-1) 0 ((Equiv.cast (D.homs M N (-1)) f).val) = _
  rfl

/-- The closed degree-zero homogeneous map of a morphism of differential graded modules. -/
noncomputable def homogeneousOfHom (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    D.category.Hom (D.objects.symm ▸ M) (D.objects.symm ▸ N) 0 :=
  (Equiv.cast (D.homs M N 0)).symm
    ⟨Cochain.ofHom f.toHomologicalComplex, actionLinear_ofHom A f⟩

/-- The homogeneous map of a morphism has the morphism itself as underlying cochain. -/
theorem homogeneousOfHom_underlying (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    underlyingCochain A D (homogeneousOfHom A D f) = Cochain.ofHom f.toHomologicalComplex :=
  congrArg Subtype.val ((Equiv.cast (D.homs M N 0)).apply_symm_apply _)

/-- The homogeneous map of a morphism of differential graded modules is closed. -/
theorem d_homogeneousOfHom (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    D.category.d (homogeneousOfHom A D f) = 0 := by
  apply underlyingCochain_injective A D
  rw [underlyingCochain_zero]
  change (D.homs M N (0 + 1) ▸ D.category.d (homogeneousOfHom A D f)).val = 0
  rw [eq_of_heq (D.differential M N 0 (homogeneousOfHom A D f))]
  change δ 0 1 (underlyingCochain A D (homogeneousOfHom A D f)) = 0
  rw [homogeneousOfHom_underlying]
  simp

/-- The cocycle of the differential graded category attached to a morphism of differential
graded modules. -/
noncomputable def cocycleOfHom (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    D.category.Cocycle (D.objects.symm ▸ M) (D.objects.symm ▸ N) :=
  ⟨homogeneousOfHom A D f, d_homogeneousOfHom A D f⟩

/-! ### Homogeneous morphisms as cochains, indexed by the objects of the category -/

/-- The two readings of the cochain underlying a degree-zero homogeneous morphism agree. -/
private theorem cochainOf_moduleMap (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (f : D.category.Hom (D.objects.symm ▸ M) (D.objects.symm ▸ N) 0) :
    HEq (cochainOf A D f) (underlyingCochain A D f) := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  rfl

/-- Passing to underlying cochains respects differences. -/
private theorem bridgeUnderlying_sub (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (_B : DGCategory.BinaryBiproductData D.category
      (D.objects.symm ▸ M) (D.objects.symm ▸ M))
    (f g : D.category.Hom (D.objects.symm ▸ M) (D.objects.symm ▸ N) n) :
    underlyingCochain A D (f - g) = underlyingCochain A D f - underlyingCochain A D g := by
  have h := underlyingCochain_add A D (f - g) g
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-! ### Homotopies as homogeneous morphisms of degree `-1` -/

/-- The degree `-1` cochain of a homotopy between morphisms of differential graded modules. -/
private noncomputable def bridgeHomotopyCochain {M N : DifferentialGradedModule.{u, v, w} A}
    {f g : M ⟶ N} (H : Homotopy f g) : Cochain M.complex N.complex (-1) :=
  Cochain.mk (fun p q hpq => H.app p ≫
    eqToHom (congrArg N.complex.X (show p - 1 = q by omega)))

/-- Heterogeneously equal sections of a graded sheaf of modules become equal after transport to
a common degree. -/
private theorem bridgeHeqAfterTransport
    (F : ℤ → SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {i j k : ℤ}
    (hi : i = k) (hj : j = k) (U : X.Cᵒᵖ)
    {x : (F i).val.obj U} {y : (F j).val.obj U} (h : x ≍ y) :
    ((eqToHom (congrArg F hi)).val.app U) x = ((eqToHom (congrArg F hj)).val.app U) y := by
  cases hi
  cases hj
  exact eq_of_heq h

/-- The cochain of a homotopy commutes with the action. -/
private theorem bridgeHomotopyActionLinear {M N : DifferentialGradedModule.{u, v, w} A}
    {f g : M ⟶ N} (H : Homotopy f g) :
    IsActionLinear A (bridgeHomotopyCochain A H) := by
  intro p q m hpq U x a
  have hq : q = p - 1 := by omega
  cases hq
  have hh := H.map_mul p m U x a
  have hc := bridgeHeqAfterTransport N.complex.X
    (show (p + m) - 1 = (p - 1) + m by omega) rfl U hh
  simpa [bridgeHomotopyCochain, Cochain.mk, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    Category.comp_id] using heq_of_eq hc

/-- The homogeneous morphism of degree `-1` attached to a homotopy. -/
private noncomputable def bridgeHomotopyMap (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {f g : M ⟶ N} (H : Homotopy f g) :
    D.category.Hom (D.objects.symm ▸ M) (D.objects.symm ▸ N) (-1) :=
  (Equiv.cast (D.homs M N (-1))).symm
    ⟨bridgeHomotopyCochain A H, bridgeHomotopyActionLinear A H⟩

/-- The homogeneous morphism of a homotopy has the homotopy's cochain as underlying cochain. -/
private theorem bridgeHomotopyMap_underlying (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {f g : M ⟶ N} (H : Homotopy f g) :
    underlyingCochain A D (bridgeHomotopyMap A D H) = bridgeHomotopyCochain A H :=
  congrArg Subtype.val ((Equiv.cast (D.homs M N (-1))).apply_symm_apply _)

/-- The homotopy of underlying complexes attached to a homotopy of differential graded modules. -/
private noncomputable def bridgeComplexHomotopy {M N : DifferentialGradedModule.{u, v, w} A}
    {f g : M ⟶ N} (H : Homotopy f g) :
    _root_.Homotopy f.toHomologicalComplex g.toHomologicalComplex := by
  let hom : ∀ i j, M.complex.X i ⟶ N.complex.X j := fun i j =>
    if hij : i - 1 = j then H.app i ≫ eqToHom (congrArg N.complex.X hij) else 0
  refine ⟨hom, ?_, ?_⟩
  · intro i j hij
    dsimp [hom]
    split
    · rename_i h
      apply False.elim
      apply hij
      change j + 1 = i
      omega
    · rfl
  · intro n
    have h₁ : hom (n + 1) n = H.app (n + 1) ≫ eqToHom
        (congrArg N.complex.X (show (n + 1) - 1 = n by omega)) := by
      simp [hom, dite_eq_left (show (n + 1) - 1 = n by omega)]
    have h₂ : hom n (n - 1) = H.app n := by
      simp [hom]
    rw [dNext_eq hom (by simp : (ComplexShape.up ℤ).Rel n (n + 1)),
      prevD_eq hom (by simp : (ComplexShape.up ℤ).Rel (n - 1) n), h₁, h₂]
    calc
      f.toHomologicalComplex.f n =
          H.app n ≫ N.complex.d (n - 1) n +
            (M.complex.d n (n + 1) ≫ H.app (n + 1)) ≫
              eqToHom (congrArg N.complex.X (show (n + 1) - 1 = n by omega)) +
            g.toHomologicalComplex.f n := sub_eq_iff_eq_add.mp (H.comm n)
      _ = (M.complex.d n (n + 1) ≫ H.app (n + 1)) ≫
            eqToHom (congrArg N.complex.X (show (n + 1) - 1 = n by omega)) +
            H.app n ≫ N.complex.d (n - 1) n + g.toHomologicalComplex.f n := by
        rw [Category.assoc]
        abel

/-- Homotopic morphisms of differential graded modules have homotopic cocycles. -/
private theorem bridgeHomotopyMap_homotopic (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (B : DGCategory.BinaryBiproductData D.category
      (D.objects.symm ▸ M) (D.objects.symm ▸ M))
    {f g : M ⟶ N} (H : Homotopy f g) :
    D.category.Homotopic (cocycleOfHom A D f) (cocycleOfHom A D g) := by
  refine ⟨bridgeHomotopyMap A D H, ?_⟩
  apply underlyingCochain_injective A D
  have hcf : (cocycleOfHom A D f).val = homogeneousOfHom A D f := rfl
  have hcg : (cocycleOfHom A D g).val = homogeneousOfHom A D g := rfl
  rw [hcf, hcg]
  rw [bridgeUnderlying_sub A D B, bridgeUnderlying_d']
  have hco : Cochain.ofHomotopy (bridgeComplexHomotopy A H) = bridgeHomotopyCochain A H := by
    ext p q hpq
    simp [bridgeComplexHomotopy, bridgeHomotopyCochain, Cochain.ofHomotopy,
      dite_eq_left (show p - 1 = q by omega), SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hδ := δ_ofHomotopy (bridgeComplexHomotopy A H)
  rw [hco] at hδ
  rw [bridgeHomotopyMap_underlying]
  change underlyingCochain A D (homogeneousOfHom A D f) -
      underlyingCochain A D (homogeneousOfHom A D g) = δ (-1) 0 (bridgeHomotopyCochain A H)
  rw [homogeneousOfHom_underlying, homogeneousOfHom_underlying]
  exact hδ.symm

/-! ### The two correspondences are bijective -/

/-- The morphism of differential graded modules attached to a closed degree-zero cocycle. -/
private noncomputable def cocycleToModule (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (c : D.category.Cocycle (D.objects.symm ▸ M) (D.objects.symm ▸ N)) : M ⟶ N where
  toHomologicalComplex := Cocycle.homOf (Cocycle.mk (underlyingCochain A D c.val) 1 rfl (by
    have hd := bridgeUnderlying_d A D c.val
    rw [c.property, underlyingCochain_zero] at hd
    exact hd.symm))
  map_mul p m U x a :=
    eq_of_heq ((Equiv.cast (D.homs M N 0) c.val).property p p m (add_zero p) U x a)

/-- The morphism of a cocycle has the cocycle's cochain as underlying cochain. -/
private theorem cocycleToModule_underlying (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (c : D.category.Cocycle (D.objects.symm ▸ M) (D.objects.symm ▸ N)) :
    Cochain.ofHom (cocycleToModule A D c).toHomologicalComplex =
      underlyingCochain A D c.val := Cocycle.cochain_ofHom_homOf_eq_coe _

/-- The cocycle of the morphism attached to a cocycle is that cocycle. -/
private theorem cocycleOfHom_cocycleToModule (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (c : D.category.Cocycle (D.objects.symm ▸ M) (D.objects.symm ▸ N)) :
    cocycleOfHom A D (cocycleToModule A D c) = c :=
  Subtype.ext (underlyingCochain_injective A D
    ((homogeneousOfHom_underlying A D _).trans (cocycleToModule_underlying A D c)))

/-- Morphisms of differential graded modules are exactly the closed degree-zero cocycles. -/
private theorem cocycleOfHom_bijective (D : DGCategoryData.{u, v, w} A)
    (M N : DifferentialGradedModule.{u, v, w} A) :
    Function.Bijective (cocycleOfHom A D (M := M) (N := N)) := by
  constructor
  · intro f g h
    have hc := congrArg (fun c => underlyingCochain A D c.val) h
    change underlyingCochain A D (homogeneousOfHom A D f) =
      underlyingCochain A D (homogeneousOfHom A D g) at hc
    rw [homogeneousOfHom_underlying, homogeneousOfHom_underlying] at hc
    have hfg : f.toHomologicalComplex = g.toHomologicalComplex :=
      (Cocycle.equivHom M.complex N.complex).injective (Subtype.ext hc)
    cases f
    cases g
    cases hfg
    rfl
  · exact fun c => ⟨cocycleToModule A D c, cocycleOfHom_cocycleToModule A D c⟩

/-- The cocycle of a composite is the composite of the cocycles. -/
theorem cocycleOfHom_comp (D : DGCategoryData.{u, v, w} A)
    {M N P : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) (g : N ⟶ P) :
    cocycleOfHom A D (f ≫ g) =
      D.category.compCocycle (cocycleOfHom A D g) (cocycleOfHom A D f) := by
  apply Subtype.ext
  apply underlyingCochain_injective A D
  change underlyingCochain A D (homogeneousOfHom A D (f ≫ g)) =
    underlyingCochain A D
      (D.category.comp rfl (homogeneousOfHom A D g) (homogeneousOfHom A D f))
  rw [underlyingCochain_comp, homogeneousOfHom_underlying,
    homogeneousOfHom_underlying, homogeneousOfHom_underlying, ← Cochain.ofHom_comp]
  rfl

/-- The cocycle of an identity morphism is the identity. -/
theorem cocycleOfHom_id (D : DGCategoryData.{u, v, w} A)
    (M : DifferentialGradedModule.{u, v, w} A) :
    cocycleOfHom A D (𝟙 M) = ⟨D.category.id (D.objects.symm ▸ M), D.category.d_id _⟩ :=
  Subtype.ext (underlyingCochain_injective A D
    ((homogeneousOfHom_underlying A D (𝟙 M)).trans (eq_of_heq (D.identity M)).symm))

/-- A component of a cochain is unchanged by transporting its target degree. -/
private theorem bridgeCochain_v_comp_eqToHom {B : Type*} [Category B] [Preadditive B]
    {M N : CochainComplex B ℤ} {k i j j' : ℤ}
    (c : Cochain M N k) (h : i + k = j) (h' : i + k = j') (e : j = j') :
    c.v i j h ≫ eqToHom (congrArg N.X e) = c.v i j' h' := by
  cases e
  simp

/-- Two components of a cochain at equal target degrees agree on sections. -/
private theorem bridgeCochain_app_heq
    {M N : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {k i j j' : ℤ} (c : Cochain M N k)
    (h : i + k = j) (h' : i + k = j') (e : j = j')
    (U : X.Cᵒᵖ) (x : (M.X i).val.obj U) :
    (c.v i j h).val.app U x ≍ (c.v i j' h').val.app U x := by
  cases e
  rfl

/-- Two morphisms of differential graded modules are homotopic exactly when their cocycles
are homotopic in the differential graded category. -/
theorem cocycleOfHom_homotopic_iff (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (B : DGCategory.BinaryBiproductData D.category
      (D.objects.symm ▸ M) (D.objects.symm ▸ M))
    (f g : M ⟶ N) :
    D.category.Homotopic (cocycleOfHom A D f) (cocycleOfHom A D g) ↔ Homotopic f g := by
  constructor
  · rintro ⟨h, hh⟩
    let c := underlyingCochain A D h
    have hd : Cochain.ofHom f.toHomologicalComplex -
        Cochain.ofHom g.toHomologicalComplex = δ (-1) 0 c := by
      have h' := congrArg (underlyingCochain A D) hh
      rw [bridgeUnderlying_sub A D B, bridgeUnderlying_d'] at h'
      dsimp only [cocycleOfHom] at h'
      rwa [homogeneousOfHom_underlying, homogeneousOfHom_underlying] at h'
    refine ⟨{ app := fun n => c.v n (n - 1) (by omega)
              map_mul := ?_
              comm := ?_ }⟩
    · intro n m U x a
      have hp := (Equiv.cast (D.homs M N (-1)) h).property n (n - 1) m (by omega) U x a
      exact (bridgeCochain_app_heq c (by omega) (by omega)
        (show n + m - 1 = (n - 1) + m by omega) U _).trans hp
    · intro n
      have hn := Cochain.congr_v hd n n (add_zero n)
      rw [δ_v (-1) 0 rfl c n n (add_zero n) (n - 1) (n + 1) rfl rfl] at hn
      simp only [Cochain.sub_v, Cochain.ofHom_v, Int.negOnePow_zero, one_smul] at hn
      rw [hn]
      congr 1
      rw [Category.assoc, bridgeCochain_v_comp_eqToHom]
      all_goals omega
  · rintro ⟨h⟩
    exact bridgeHomotopyMap_homotopic A D B h

/-! ### The identification of the two homotopy categories -/

/-- The functor sending a right differential graded module to itself, viewed as an object of
the homotopy category of their differential graded category. -/
noncomputable def toDGHomotopyCategory :
    DifferentialGradedModule.{u, v, w} A ⥤ (dgCategoryData.{u, v, w} A).category.K where
  obj M := asObject A M
  map f := Quotient.mk _ (cocycleOfHom A (dgCategoryData A) f)
  map_id M := congrArg (Quotient.mk _) (cocycleOfHom_id A _ M)
  map_comp f g := congrArg (Quotient.mk _) (cocycleOfHom_comp A _ f g)

/-- The functor from the homotopy category of right differential graded modules to the homotopy
category of their differential graded category. -/
noncomputable def homotopyCategoryToDG :
    HomotopyCategory.{u, v, w} A ⥤ (dgCategoryData.{u, v, w} A).category.K :=
  CategoryTheory.Quotient.lift _ (toDGHomotopyCategory A) fun _ _ f g h =>
    Quotient.sound ((cocycleOfHom_homotopic_iff A _
      (Classical.choice (hasBinaryBiproducts A _ _)) f g).2 h)

/-- The comparison functor is bijective on arrows. -/
theorem homotopyCategoryToDG_map_bijective
    (M N : HomotopyCategory.{u, v, w} A) :
    Function.Bijective ((homotopyCategoryToDG A).map (X := M) (Y := N)) := by
  cases M with | mk M =>
  cases N with | mk N =>
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective g
    exact (HomotopyCategory.quotient_map_eq_iff f g).2 ((cocycleOfHom_homotopic_iff A _
      (Classical.choice (hasBinaryBiproducts A _ _)) f g).1 (Quotient.exact h))
  · intro c
    induction c using Quotient.inductionOn with | h c =>
    obtain ⟨f, rfl⟩ := (cocycleOfHom_bijective A _ M N).surjective c
    exact ⟨(HomotopyCategory.quotient A).map f, rfl⟩

/-- The comparison functor is fully faithful. -/
noncomputable def homotopyCategoryToDGFullyFaithful :
    (homotopyCategoryToDG.{u, v, w} A).FullyFaithful where
  preimage {M N} := (Equiv.ofBijective _ (homotopyCategoryToDG_map_bijective A M N)).symm
  map_preimage _ :=
    (Equiv.ofBijective _ (homotopyCategoryToDG_map_bijective A _ _)).apply_symm_apply _
  preimage_map _ :=
    (Equiv.ofBijective _ (homotopyCategoryToDG_map_bijective A _ _)).symm_apply_apply _

/-- The comparison functor is essentially surjective. -/
instance homotopyCategoryToDG_essSurj :
    (homotopyCategoryToDG.{u, v, w} A).EssSurj where
  mem_essImage Y := ⟨(HomotopyCategory.quotient A).obj (asModule A Y),
    ⟨eqToIso (asObject_asModule A Y)⟩⟩

/-- The comparison functor is full. -/
instance homotopyCategoryToDG_full : (homotopyCategoryToDG.{u, v, w} A).Full :=
  (homotopyCategoryToDGFullyFaithful A).full

/-- The comparison functor is faithful. -/
instance homotopyCategoryToDG_faithful : (homotopyCategoryToDG.{u, v, w} A).Faithful :=
  (homotopyCategoryToDGFullyFaithful A).faithful

/-- The comparison functor is an equivalence. -/
instance homotopyCategoryToDG_isEquivalence :
    (homotopyCategoryToDG.{u, v, w} A).IsEquivalence := {}

/-- The homotopy category of right differential graded modules over a sheaf of differential
graded algebras is the homotopy category of their differential graded category. -/
@[stacks 0FRZ]
noncomputable def homotopyCategoryEquivalence :
    HomotopyCategory.{u, v, w} A ≌ (dgCategoryData.{u, v, w} A).category.K :=
  (homotopyCategoryToDG A).asEquivalence

/-- The identification of the two homotopy categories sends a differential graded module to
itself. -/
@[stacks 0FRZ]
theorem homotopyCategoryEquivalence_obj (M : DifferentialGradedModule.{u, v, w} A) :
    (homotopyCategoryEquivalence A).functor.obj ((HomotopyCategory.quotient A).obj M) =
      asObject A M := rfl

/-- The identification of the two homotopy categories sends the homotopy class of a morphism
to the homotopy class of the closed degree-zero homogeneous map with the same underlying
cochain. -/
@[stacks 0FRZ]
theorem homotopyCategoryEquivalence_map {M N : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) :
    ∃ c : (dgCategoryData.{u, v, w} A).category.Cocycle (asObject A M) (asObject A N),
      HEq (asCochain A c.val) (Cochain.ofHom f.toHomologicalComplex) ∧
        HEq ((homotopyCategoryEquivalence A).functor.map
            ((HomotopyCategory.quotient A).map f))
          (Quotient.mk ((dgCategoryData A).category.homotopySetoid _ _) c) :=
  ⟨cocycleOfHom A (dgCategoryData A) f,
    (cochainOf_moduleMap A (dgCategoryData A) (homogeneousOfHom A _ f)).trans
      (heq_of_eq (homogeneousOfHom_underlying A _ f)), HEq.rfl⟩

/-! ### The triangulated structure of the differential graded homotopy category -/

/-- A cone situation on the differential graded category of right differential graded modules
whose shifts are the canonical ones. -/
noncomputable def dgConeSituation :
    DGCategory.ConeSituation (dgCategoryData.{u, v, w} A).category :=
  Classical.choose (coneSituation.{u, v, w} A)

/-- The chosen cone situation has the canonical differential graded shifts. -/
theorem dgConeSituation_shift :
    (dgConeSituation.{u, v, w} A).shift = (shiftAxiomB.{u, v, w} A).axiomB :=
  Classical.choose_spec (coneSituation.{u, v, w} A)

/-- The homotopy category of the differential graded category of right differential graded
modules is preadditive. -/
@[instance_reducible]
noncomputable instance dgHomotopyPreadditive :
    Preadditive (dgCategoryData.{u, v, w} A).category.K :=
  DGCategory.homotopyPreadditive _

/-- The translation functors of the homotopy category of the differential graded category of
right differential graded modules. -/
@[instance_reducible]
noncomputable instance dgHomotopyHasShift :
    HasShift (dgCategoryData.{u, v, w} A).category.K ℤ :=
  (dgConeSituation A).shift.kShift

/-- The homotopy category of the differential graded category of right differential graded
modules has a zero object. -/
instance dgHomotopyHasZeroObject :
    HasZeroObject (dgCategoryData.{u, v, w} A).category.K :=
  DGCategory.homotopyHasZeroObject _ (dgConeSituation A)

/-- Every translation functor of the differential graded homotopy category is additive. -/
instance dgHomotopyShiftAdditive (n : ℤ) :
    (shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).Additive :=
  DGCategory.homotopyShiftAdditive _ (dgConeSituation A) n

/-- The differential graded homotopy category is pretriangulated, with the triangles of
admissible short exact sequences as its distinguished triangles. -/
@[instance_reducible]
noncomputable instance dgHomotopyPretriangulated :
    Pretriangulated (dgCategoryData.{u, v, w} A).category.K :=
  DGCategory.homotopyPretriangulated _ (dgConeSituation A)

/-- The differential graded homotopy category satisfies the octahedron axiom. -/
instance dgHomotopyIsTriangulated :
    IsTriangulated (dgCategoryData.{u, v, w} A).category.K :=
  DGCategory.homotopyCategory_isTriangulated _ (dgConeSituation A)

/-- A triangle of the differential graded homotopy category is distinguished exactly when it is
isomorphic to the triangle of an admissible short exact sequence. -/
theorem dgHomotopy_distinguished_iff
    (T : Pretriangulated.Triangle (dgCategoryData.{u, v, w} A).category.K) :
    T ∈ Pretriangulated.distinguishedTriangles
        (C := (dgCategoryData.{u, v, w} A).category.K) ↔
      DGCategory.IsDistinguishedTriangle _ (dgConeSituation A) T := by
  have h := DGCategory.distinguishedTriangles_homotopyPretriangulated
    (dgCategoryData.{u, v, w} A).category (dgConeSituation A)
  exact Set.ext_iff.mp h T

/-! ### The triangulated structure of the homotopy category of differential graded modules -/

/-- The comparison functor is additive, since an equivalence preserves binary products and
zero morphisms. -/
instance homotopyCategoryToDG_additive : (homotopyCategoryToDG.{u, v, w} A).Additive := by
  have : HasFiniteProducts (HomotopyCategory.{u, v, w} A) :=
    hasFiniteProducts_of_hasProducts.{w} _
  exact Functor.additive_of_preserves_binary_products _

/-- A differential graded module representing an object of the differential graded homotopy
category, as an object of the homotopy category of modules. -/
noncomputable def dgObjPreimage (Y : (dgCategoryData.{u, v, w} A).category.K) :
    HomotopyCategory.{u, v, w} A :=
  (HomotopyCategory.quotient A).obj (asModule A Y)

/-- The comparison functor returns an object of the differential graded homotopy category to
itself. -/
theorem homotopyCategoryToDG_obj_dgObjPreimage
    (Y : (dgCategoryData.{u, v, w} A).category.K) :
    (homotopyCategoryToDG A).obj (dgObjPreimage A Y) = Y :=
  asObject_asModule A Y

/-- The degree-`n` translation functor of the homotopy category of right differential graded
modules, lifted from the differential graded shift. -/
noncomputable def homotopyShiftFunctor (n : ℤ) :
    HomotopyCategory.{u, v, w} A ⥤ HomotopyCategory.{u, v, w} A :=
  (homotopyCategoryToDGFullyFaithful A).liftEndofunctor (dgObjPreimage A)
    (homotopyCategoryToDG_obj_dgObjPreimage A)
    (shiftFunctor (dgCategoryData.{u, v, w} A).category.K n)

/-- The lifted translation functor is intertwined with the differential graded shift. -/
noncomputable def homotopyShiftFunctorIso (n : ℤ) :
    homotopyShiftFunctor A n ⋙ homotopyCategoryToDG A ≅
      homotopyCategoryToDG A ⋙ shiftFunctor (dgCategoryData.{u, v, w} A).category.K n :=
  (homotopyCategoryToDGFullyFaithful A).liftEndofunctorIso (dgObjPreimage A)
    (homotopyCategoryToDG_obj_dgObjPreimage A)
    (shiftFunctor (dgCategoryData.{u, v, w} A).category.K n)

namespace HomotopyCategory

/-- The translation functors of the homotopy category of right differential graded modules,
lifted from the differential graded shifts along the identification of the two homotopy
categories. -/
@[instance_reducible, stacks 0FS7 "part (1): the shift functors"]
noncomputable instance instHasShift : HasShift (HomotopyCategory.{u, v, w} A) ℤ :=
  (homotopyCategoryToDGFullyFaithful A).hasShift (homotopyShiftFunctor A)
    (homotopyShiftFunctorIso A)

end HomotopyCategory

/-- The comparison functor commutes with the translation functors. -/
@[instance_reducible]
noncomputable instance homotopyCategoryToDG_commShift :
    (homotopyCategoryToDG.{u, v, w} A).CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful (homotopyCategoryToDGFullyFaithful A)
    (homotopyShiftFunctor A) (homotopyShiftFunctorIso A)

namespace HomotopyCategory

/-- Every translation functor of the homotopy category of right differential graded modules is
additive. -/
instance shiftFunctor_additive (n : ℤ) :
    (shiftFunctor (HomotopyCategory.{u, v, w} A) n).Additive :=
  (homotopyCategoryToDGFullyFaithful A).liftEndofunctor_additive (dgObjPreimage A)
    (homotopyCategoryToDG_obj_dgObjPreimage A)
    (shiftFunctor (dgCategoryData.{u, v, w} A).category.K n)

/-- The homotopy category of right differential graded modules is pretriangulated. -/
@[instance_reducible, stacks 0FS7 "the pre-triangulated structure"]
noncomputable instance instPretriangulated :
    Pretriangulated (HomotopyCategory.{u, v, w} A) :=
  Pretriangulated.ofEquivalence (homotopyCategoryToDG A)

/-- **Tag 0FS7.** The homotopy category of right differential graded modules over a sheaf of
differential graded algebras on a ringed site is a triangulated category. -/
@[stacks 0FS7]
instance instIsTriangulated : IsTriangulated (HomotopyCategory.{u, v, w} A) := by
  let _ : (homotopyCategoryToDG.{u, v, w} A).IsTriangulated := ⟨fun _ h => h⟩
  exact IsTriangulated.of_fully_faithful_triangulated_functor (homotopyCategoryToDG A)

/-- A triangle of the homotopy category is distinguished exactly when its image in the
differential graded homotopy category is. -/
theorem mem_distinguishedTriangles_iff
    (T : Pretriangulated.Triangle (HomotopyCategory.{u, v, w} A)) :
    T ∈ Pretriangulated.distinguishedTriangles (C := HomotopyCategory.{u, v, w} A) ↔
      (homotopyCategoryToDG A).mapTriangle.obj T ∈
        Pretriangulated.distinguishedTriangles
          (C := (dgCategoryData.{u, v, w} A).category.K) := Iff.rfl

end HomotopyCategory

/-- An admissible short exact sequence of right differential graded modules gives a triangle of
their homotopy category whose image is the associated triangle. -/
private theorem exists_quotientTriangle
    (M N P : DifferentialGradedModule.{u, v, w} A)
    (E : DGCategory.GradedSplitShortExact (A := (dgCategoryData.{u, v, w} A).category)
      (asObject A M) (asObject A N) (asObject A P)) :
    ∃ (f : M ⟶ N) (g : N ⟶ P)
      (δ : (HomotopyCategory.quotient A).obj P ⟶
        (shiftFunctor (HomotopyCategory.{u, v, w} A) (1 : ℤ)).obj
          ((HomotopyCategory.quotient A).obj M)),
      cocycleOfHom A (dgCategoryData A) f = E.a ∧
        cocycleOfHom A (dgCategoryData A) g = E.b ∧
        Nonempty ((homotopyCategoryToDG A).mapTriangle.obj
            (Pretriangulated.Triangle.mk ((HomotopyCategory.quotient A).map f)
              ((HomotopyCategory.quotient A).map g) δ) ≅
          DGCategory.GradedSplitShortExact.associatedKTriangle (dgConeSituation A).shift E) := by
  let F := homotopyCategoryToDG.{u, v, w} A
  let V := DGCategory.GradedSplitShortExact.associatedKTriangle (dgConeSituation A).shift E
  refine ⟨cocycleToModule A (dgCategoryData A) E.a, cocycleToModule A (dgCategoryData A) E.b,
    F.preimage (V.mor₃ ≫ (F.commShiftIso (1 : ℤ)).inv.app
      ((HomotopyCategory.quotient A).obj M)),
    cocycleOfHom_cocycleToModule A _ E.a, cocycleOfHom_cocycleToModule A _ E.b, ?_⟩
  have key : ∀ {M N : DifferentialGradedModule.{u, v, w} A}
      (c : (dgCategoryData.{u, v, w} A).category.Cocycle (asObject A M) (asObject A N)),
      F.map ((HomotopyCategory.quotient A).map (cocycleToModule A (dgCategoryData A) c)) =
        Quotient.mk _ c := fun c =>
    congrArg (Quotient.mk _) (cocycleOfHom_cocycleToModule A (dgCategoryData A) c)
  refine ⟨Pretriangulated.Triangle.isoMk _ V (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_⟩
  · exact (Category.comp_id _).trans ((key E.a).trans (Category.id_comp V.mor₁).symm)
  · exact (Category.comp_id _).trans ((key E.b).trans (Category.id_comp V.mor₂).symm)
  · change (F.map (F.preimage (V.mor₃ ≫ (F.commShiftIso (1 : ℤ)).inv.app
        ((HomotopyCategory.quotient A).obj M))) ≫
      (F.commShiftIso (1 : ℤ)).hom.app ((HomotopyCategory.quotient A).obj M)) ≫
        (shiftFunctor (dgCategoryData.{u, v, w} A).category.K (1 : ℤ)).map (𝟙 _) =
      𝟙 _ ≫ V.mor₃
    simp only [Functor.comp_obj, Functor.map_preimage, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]
    exact CategoryTheory.comp_inv_hom_app (F.commShiftIso (1 : ℤ))
      ((HomotopyCategory.quotient A).obj M) V.mor₃

namespace HomotopyCategory

/-- A triangle of the homotopy category of right differential graded modules is distinguished
exactly when it is isomorphic to the triangle built from an admissible short exact sequence of
right differential graded modules, the connecting arrow being the class of `π d s`. -/
@[stacks 0FS7 "part (2): the distinguished triangles"]
theorem distinguished_iff (T : Pretriangulated.Triangle (HomotopyCategory.{u, v, w} A)) :
    T ∈ Pretriangulated.distinguishedTriangles (C := HomotopyCategory.{u, v, w} A) ↔
      ∃ (M N P : DifferentialGradedModule.{u, v, w} A) (f : M ⟶ N) (g : N ⟶ P)
        (δ : (quotient A).obj P ⟶
          (shiftFunctor (HomotopyCategory.{u, v, w} A) (1 : ℤ)).obj ((quotient A).obj M))
        (E : DGCategory.GradedSplitShortExact (A := (dgCategoryData.{u, v, w} A).category)
          (asObject A M) (asObject A N) (asObject A P)),
        cocycleOfHom A (dgCategoryData A) f = E.a ∧
          cocycleOfHom A (dgCategoryData A) g = E.b ∧
          Nonempty (T ≅ Pretriangulated.Triangle.mk ((quotient A).map f)
            ((quotient A).map g) δ) ∧
          Nonempty ((homotopyCategoryToDG A).mapTriangle.obj
              (Pretriangulated.Triangle.mk ((quotient A).map f) ((quotient A).map g) δ) ≅
            DGCategory.GradedSplitShortExact.associatedKTriangle
              (dgConeSituation A).shift E) := by
  have hsurj : Function.Surjective (asObject.{u, v, w} A) :=
    fun Y => ⟨asModule A Y, asObject_asModule A Y⟩
  rw [mem_distinguishedTriangles_iff, dgHomotopy_distinguished_iff]
  constructor
  · rintro ⟨x, y, z, E, ⟨e⟩⟩
    obtain ⟨M, rfl⟩ := hsurj x
    obtain ⟨N, rfl⟩ := hsurj y
    obtain ⟨P, rfl⟩ := hsurj z
    obtain ⟨f, g, δ, hf, hg, ⟨e'⟩⟩ := exists_quotientTriangle A M N P E
    exact ⟨M, N, P, f, g, δ, E, hf, hg,
      ⟨(homotopyCategoryToDG A).mapTriangle.preimageIso (e ≪≫ e'.symm)⟩, ⟨e'⟩⟩
  · rintro ⟨M, N, P, f, g, δ, E, -, -, ⟨e⟩, ⟨e'⟩⟩
    exact ⟨asObject A M, asObject A N, asObject A P, E,
      ⟨(homotopyCategoryToDG A).mapTriangle.mapIso e ≪≫ e'⟩⟩

/-- The degree-one translation of the homotopy category is the shift of differential graded
modules of Stacks 0FS5. -/
@[stacks 0FS7 "part (1): the shift functors are those of Section 24.20"]
theorem shiftFunctor_obj (M : DifferentialGradedModule.{u, v, w} A) :
    (shiftFunctor (HomotopyCategory.{u, v, w} A) (1 : ℤ)).obj ((quotient A).obj M) =
      (quotient A).obj (shift M) := by
  change (quotient A).obj (asModule A
    ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K (1 : ℤ)).obj (asObject A M))) = _
  rw [(dgConeSituation A).shift.kShift_functor]
  refine congrArg (quotient A).obj ?_
  have h : asModule A (((dgConeSituation A).shift.shiftFunctor (1 : ℤ)).obj (asObject A M)) =
      asModule A (((shiftAxiomB A).axiomB.shiftFunctor (1 : ℤ)).obj (asObject A M)) := by
    rw [dgConeSituation_shift]
  exact h.trans ((shiftAxiomB A).shift_one M)

end HomotopyCategory

end SheafOfModules.DifferentialGradedModule
