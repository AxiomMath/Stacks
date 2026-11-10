module

public import Mathlib.RingTheory.Flat.Equalizer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineInvariantFlat

/-!
# Invariant functions after a flat extension of the invariant ring

Extending the invariant ring of an affine groupoid scheme along a flat ring map creates no new
invariant functions: the canonical map from the new base ring to the invariant functions of the
base-changed groupoid is an isomorphism.

## Main results

* `AlgebraicGeometry.GroupoidScheme.canonicalMapToInvariantFunctions_bijective_of_flat`: the
  canonical map from the new base ring to the invariant functions is bijective.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Swapping the two tensor factors exchanges extending scalars on the right with extending
them on the left. -/
private theorem tensorProduct_comm_map {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B] (h : A →ₐ[R] B) (x : A ⊗[R] S) :
    Algebra.TensorProduct.comm R B S (Algebra.TensorProduct.map h (AlgHom.id R S) x) =
      Algebra.TensorProduct.map (AlgHom.id S S) h (Algebra.TensorProduct.comm R A S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a s => simp
  | add x y hx hy => simp [hx, hy]

/-- Alias of `AlgebraicGeometry.flat_tensor_equalizer_bijective`. -/
private alias flat_tensorEqualizer_bijective :=
  AlgebraicGeometry.flat_tensor_equalizer_bijective

/-- The global sections of `Spec` of a ring map, read through the canonical identification. -/
private theorem commRingCatIsoToRingEquiv_specMap {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (y : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv ((Spec.map φ).appTop.hom y) =
      φ.hom ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv y) :=
  congrArg (fun k : CommRingCat.of Γ(Spec R, ⊤) ⟶ T => k.hom y) (Scheme.ΓSpecIso_naturality φ)

/-- The canonical identification of a ring with the global sections of its spectrum, composed
with its inverse. -/
private theorem commRingCatIsoToRingEquiv_inv_apply (R : CommRingCat.{u}) (x : R) :
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv ((Scheme.ΓSpecIso R).inv.hom x) = x := by
  change (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom x) = x
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    congrArg (fun k : R ⟶ R => k.hom x) (Iso.inv_hom_id (Scheme.ΓSpecIso R))

section BaseChanged

variable {S : Scheme.{u}} {G : GroupoidScheme S} {C' : Type u} [CommRing C']
  [Algebra (invariantRing G) C'] (G' : AffineInvariantBaseChange G C')

/-- The coordinate ring of the object scheme of the base-changed groupoid, read as the tensor
product `A ⊗[C] C'`. -/
private noncomputable def objectCoordEquiv :
    Γ(G'.groupoid.objects.left, ⊤) ≃+* objectRingBaseChange G C' :=
  (asIso (Scheme.Γ.map G'.objectsIso.inv.op)).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv

/-- The coordinate ring of the arrow scheme of the base-changed groupoid, read as the tensor
product `B ⊗[C] C'`. -/
private noncomputable def arrowCoordEquiv :
    Γ(G'.groupoid.arrows.left, ⊤) ≃+* arrowRingBaseChange G C' :=
  (asIso (Scheme.Γ.map G'.arrowsIso.inv.op)).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv

/-- Reading a global section of `Spec R` through an isomorphism `e : X ≅ Spec R` and then through
`Γ(X, ⊤) ≃+* R` is the canonical identification of `Γ(Spec R, ⊤)` with `R`. -/
private theorem comp_appTop_iso_hom {X : Scheme.{u}} {R : CommRingCat.{u}} (e : X ≅ Spec R)
    (y : Γ(Spec R, ⊤)) :
    ((asIso (Scheme.Γ.map e.inv.op)).commRingCatIsoToRingEquiv.trans
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv) ((Scheme.Hom.appTop e.hom).hom y) =
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv y := by
  have hi : Scheme.Hom.appTop e.hom ≫ Scheme.Hom.appTop e.inv = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  have hinner : (Scheme.Hom.appTop e.inv).hom ((Scheme.Hom.appTop e.hom).hom y) = y := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      congrArg (fun k => k y) hi
  exact congrArg (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv hinner

private theorem objectCoordEquiv_appTop_objectsIso_hom
    (y : Γ(Spec (.of (objectRingBaseChange G C')), ⊤)) :
    objectCoordEquiv G' ((Scheme.Hom.appTop G'.objectsIso.hom).hom y) =
      (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv y :=
  comp_appTop_iso_hom G'.objectsIso y

private theorem arrowCoordEquiv_appTop_arrowsIso_hom
    (y : Γ(Spec (.of (arrowRingBaseChange G C')), ⊤)) :
    arrowCoordEquiv G' ((Scheme.Hom.appTop G'.arrowsIso.hom).hom y) =
      (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv y :=
  comp_appTop_iso_hom G'.arrowsIso y

/-- The canonical map from the new base ring to the invariant functions is, in the tensor
product description of the object ring, the inclusion of the right factor. -/
private theorem objectCoordEquiv_canonicalMap (x : C') :
    objectCoordEquiv G'
        (G'.canonicalMapToInvariantFunctions x : Γ(G'.groupoid.objects.left, ⊤)) =
      Algebra.TensorProduct.includeRight x := by
  change objectCoordEquiv G' ((Scheme.ΓSpecIso (.of C')).inv.hom x |> fun y =>
    (Scheme.Hom.appTop G'.groupoid.objects.hom).hom y) = _
  rw [← G'.objectsIso_over]
  change objectCoordEquiv G' ((Scheme.Hom.appTop G'.objectsIso.hom).hom
    ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C' →ₐ[invariantRing G]
        objectRingBaseChange G C').toRingHom))).hom
      ((Scheme.ΓSpecIso (.of C')).inv.hom x))) = _
  rw [objectCoordEquiv_appTop_objectsIso_hom, commRingCatIsoToRingEquiv_specMap,
    commRingCatIsoToRingEquiv_inv_apply]
  rfl

end BaseChanged

/-- For a flat extension of the invariant ring of an affine groupoid scheme, the canonical map
from the new base ring to the invariant functions of the base-changed groupoid is bijective. -/
@[stacks 03BK "flat_invariants"]
theorem canonicalMapToInvariantFunctions_bijective_of_flat {S : Scheme.{u}}
    {G : GroupoidScheme S} {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C'] (G' : AffineInvariantBaseChange G C') :
    Function.Bijective G'.canonicalMapToInvariantFunctions := by
  classical
  let C := invariantRing G
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let : Algebra C B := invariantRingAlgebraArrow G
  let f := sourceAlgHom G
  let g := targetAlgHom G
  let fbase := Algebra.TensorProduct.map f (AlgHom.id C C')
  let gbase := Algebra.TensorProduct.map g (AlgHom.id C C')
  let E := fbase.equalizer gbase
  let objCoord := objectCoordEquiv G'
  let arrCoord := arrowCoordEquiv G'
  let ec : C →ₐ[C] f.equalizer g :=
    { toFun := fun c => ⟨c.1, c.2⟩
      map_one' := by ext; rfl
      map_mul' _ _ := by ext; rfl
      map_zero' := by ext; rfl
      map_add' _ _ := by ext; rfl
      commutes' := by intro c; ext; rfl }
  have hec : Function.Bijective ec :=
    ⟨fun x y h ↦ Subtype.ext (congrArg Subtype.val h), fun x ↦ ⟨⟨x.1, x.2⟩, Subtype.ext rfl⟩⟩
  have hmain := flat_tensorEqualizer_bijective (R := C) (S := C') (A := A) (B := B) f g
    (AlgEquiv.ofBijective ec hec)
  have hcoord {m : G'.groupoid.arrows.left ⟶ G'.groupoid.objects.left}
      {ψ : A ⊗[C] C' →ₐ[C] B ⊗[C] C'}
      (hm : m = G'.arrowsIso.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        G'.objectsIso.inv) (x : Γ(G'.groupoid.objects.left, ⊤)) :
      arrCoord ((Scheme.Hom.appTop m).hom x) = ψ (objCoord x) := by
    rw [hm]
    change arrCoord ((Scheme.Hom.appTop G'.arrowsIso.hom).hom
      ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom ψ.toRingHom))).hom
        ((Scheme.Hom.appTop G'.objectsIso.inv).hom x))) = _
    rw [arrowCoordEquiv_appTop_arrowsIso_hom, commRingCatIsoToRingEquiv_specMap]
    rfl
  have hsrc (x : Γ(G'.groupoid.objects.left, ⊤)) :
      arrCoord (sourceMap G'.groupoid x) = fbase (objCoord x) := hcoord G'.source_eq x
  have htgt (x : Γ(G'.groupoid.objects.left, ⊤)) :
      arrCoord (targetMap G'.groupoid x) = gbase (objCoord x) := hcoord G'.target_eq x
  let invCoord : G'.invariantFunctions →+* E := RingHom.codRestrict
    (objCoord.toRingHom.comp G'.invariantFunctions.subtype) E (by
      intro x
      change fbase (objCoord x.1) = gbase (objCoord x.1)
      exact (hsrc x.1).symm.trans ((congrArg arrCoord x.2).trans (htgt x.1)))
  have hinv : Function.Bijective invCoord := by
    refine ⟨fun x y h ↦ Subtype.val_injective (objCoord.injective (congrArg Subtype.val h)),
      fun z ↦ ⟨⟨objCoord.symm z, ?_⟩, Subtype.ext (by simp [invCoord])⟩⟩
    change sourceMap G'.groupoid (objCoord.symm z) = targetMap G'.groupoid (objCoord.symm z)
    apply arrCoord.injective
    rw [hsrc, htgt, RingEquiv.apply_symm_apply]
    exact z.2
  let eInv : G'.invariantFunctions ≃+* E := RingEquiv.ofBijective invCoord hinv
  refine (eInv.bijective.of_comp_iff' G'.canonicalMapToInvariantFunctions).mp ?_
  convert hmain using 1
  exact funext fun x ↦ Subtype.ext (objectCoordEquiv_canonicalMap G' x)

end AlgebraicGeometry.GroupoidScheme

end
