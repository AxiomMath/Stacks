module

public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSpectrum

/-!
# Invariant functions after a flat extension of the invariant ring

For a groupoid scheme whose object and arrow schemes are affine, extension of scalars from its
invariant ring along a flat ring map creates no new invariant functions.

## Main results

* `AlgebraicGeometry.canonicalMapToInvariantFunctions_bijective_of_flat`: for a flat extension
  of the invariant ring, the canonical map from the extension ring to the invariant functions of
  the base-changed groupoid scheme is bijective.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids AlgebraicGeometry.GroupoidScheme


/-- For a flat extension of the base ring, the canonical map from the extension ring to the
equalizer of the two base-changed algebra maps is bijective, provided the base ring is already
the equalizer of the two original maps. -/
theorem flat_tensor_equalizer_bijective
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) [Module.Flat R S]
    (e : R ≃ₐ[R] f.equalizer g) :
    Function.Bijective (fun s : S =>
      (⟨Algebra.TensorProduct.includeRight s,
        AlgHom.mem_equalizer (Algebra.TensorProduct.map f (AlgHom.id R S))
          (Algebra.TensorProduct.map g (AlgHom.id R S)) _ |>.2 (by simp)⟩ :
       ↥((Algebra.TensorProduct.map f (AlgHom.id R S)).equalizer
         (Algebra.TensorProduct.map g (AlgHom.id R S))))) := by
  let fflip := Algebra.TensorProduct.map (AlgHom.id S S) f
  let gflip := Algebra.TensorProduct.map (AlgHom.id S S) g
  let fbase := Algebra.TensorProduct.map f (AlgHom.id R S)
  let gbase := Algebra.TensorProduct.map g (AlgHom.id R S)
  let commA := Algebra.TensorProduct.comm R A S
  let commB := Algebra.TensorProduct.comm R B S
  have hcomm (h : A →ₐ[R] B) (x : A ⊗[R] S) :
      commB ((Algebra.TensorProduct.map h (AlgHom.id R S)) x) =
        (Algebra.TensorProduct.map (AlgHom.id S S) h) (commA x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s => simp [commA, commB]
    | add x y hx hy => simp [hx, hy]
  have hcommf (x : A ⊗[R] S) : commB (fbase x) = fflip (commA x) := hcomm f x
  have hcommg (x : A ⊗[R] S) : commB (gbase x) = gflip (commA x) := hcomm g x
  let eFlip := fflip.equalizer gflip
  let eBase := fbase.equalizer gbase
  let q : eFlip →+* eBase := RingHom.codRestrict
    (commA.symm.toRingHom.comp eFlip.val) eBase (by
      intro y
      show fbase (commA.symm y) = gbase (commA.symm y)
      apply commB.injective
      calc
        commB (fbase (commA.symm y)) = fflip y := by simpa using hcommf (commA.symm y)
        _ = gflip y := y.2
        _ = commB (gbase (commA.symm y)) := by simpa using (hcommg (commA.symm y)).symm)
  have hq : Function.Bijective q := by
    refine ⟨fun x y h => Subtype.val_injective (commA.symm.injective (congrArg Subtype.val h)),
      fun z => ?_⟩
    refine ⟨⟨commA z, ?_⟩, ?_⟩
    · show fflip (commA z) = gflip (commA z)
      calc
        fflip (commA z) = commB (fbase z) := (hcommf z).symm
        _ = commB (gbase z) := congrArg commB z.2
        _ = gflip (commA z) := hcommg z
    · apply Subtype.ext
      simp [q]
  let eFlipBase : eFlip ≃+* eBase := RingEquiv.ofBijective q hq
  let eTensor := AlgHom.tensorEqualizerEquiv (R := R) S S f g
  let eCoreS := Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S)) e
  let eDom := (Algebra.TensorProduct.comm R S R).trans (Algebra.TensorProduct.lid R S)
  let eAll : S ≃+* eBase :=
    (eCoreS.symm.toRingEquiv.trans eDom.toRingEquiv).symm.trans
      (eTensor.toRingEquiv.trans eFlipBase)
  have hTensor (s : S) (x : f.equalizer g) :
      ((AlgHom.tensorEqualizer S S f g) (s ⊗ₜ[R] x) : S ⊗[R] A) = s ⊗ₜ[R] (x : A) := by
    rw [AlgHom.coe_tensorEqualizer]
    simp
  have heAll (s : S) : eAll s =
      (⟨Algebra.TensorProduct.includeRight s,
        AlgHom.mem_equalizer fbase gbase _ |>.2 (by simp [fbase, gbase])⟩ : eBase) := by
    apply Subtype.ext
    simp [eAll, eCoreS, eDom, eTensor, eFlipBase, q, eFlip, commA, hTensor]
  convert eAll.bijective using 1
  exact funext fun s => (heAll s).symm

/-- The global functions on the object scheme of a base-changed groupoid scheme, identified
with the extended object ring through the specified tensor-product presentation. -/
private noncomputable def objectRingCoord {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') :
    Γ(G'.groupoid.objects.left, ⊤) ≃+* objectRingBaseChange G C' :=
  (asIso (Scheme.Γ.map G'.objectsIso.inv.op)).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv

/-- The global functions on the arrow scheme of a base-changed groupoid scheme, identified
with the extended arrow ring through the specified tensor-product presentation. -/
private noncomputable def arrowRingCoord {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') :
    Γ(G'.groupoid.arrows.left, ⊤) ≃+* arrowRingBaseChange G C' :=
  (asIso (Scheme.Γ.map G'.arrowsIso.inv.op)).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv

/-- Pulling a function back along an isomorphism of schemes and then along its inverse recovers
the function. -/
private theorem appTop_inv_appTop_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (y : Γ(Y, ⊤)) :
    (Scheme.Hom.appTop e.inv).hom ((Scheme.Hom.appTop e.hom).hom y) = y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
  simp

/-- Pulling a function back along the presentation of the object scheme and then identifying
the result with the extended object ring recovers the affine comparison isomorphism. -/
private theorem objectRingCoord_appTop_objectsIso_hom {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C')
    (y : Γ(Spec (.of (objectRingBaseChange G C')), ⊤)) :
    objectRingCoord G' ((Scheme.Hom.appTop G'.objectsIso.hom).hom y) =
      (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv y :=
  congrArg (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv
    (appTop_inv_appTop_hom_apply G'.objectsIso y)

/-- Pulling a function back along the presentation of the arrow scheme and then identifying
the result with the extended arrow ring recovers the affine comparison isomorphism. -/
private theorem arrowRingCoord_appTop_arrowsIso_hom {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C')
    (y : Γ(Spec (.of (arrowRingBaseChange G C')), ⊤)) :
    arrowRingCoord G' ((Scheme.Hom.appTop G'.arrowsIso.hom).hom y) =
      (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv y :=
  congrArg (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv
    (appTop_inv_appTop_hom_apply G'.arrowsIso y)

/-- A morphism of the base-changed groupoid presented by a ring map `φ` acts on global functions,
in the extended coordinates, by `φ`. -/
private theorem arrowRingCoord_appTop_apply {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C')
    (φ : objectRingBaseChange G C' →+* arrowRingBaseChange G C')
    (m : G'.groupoid.arrows.left ⟶ G'.groupoid.objects.left)
    (hm : m = G'.arrowsIso.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ G'.objectsIso.inv)
    (x : Γ(G'.groupoid.objects.left, ⊤)) :
    arrowRingCoord G' ((Scheme.Hom.appTop m).hom x) = φ (objectRingCoord G' x) := by
  subst hm
  change arrowRingCoord G' ((Scheme.Hom.appTop G'.arrowsIso.hom).hom
    ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ))).hom
      ((Scheme.Hom.appTop G'.objectsIso.inv).hom x))) = _
  rw [arrowRingCoord_appTop_arrowsIso_hom]
  exact congrArg (fun k => k.hom ((Scheme.Hom.appTop G'.objectsIso.inv).hom x))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

/-- Under the identification of the object ring of a base-changed groupoid scheme with the
extended object ring, the canonical map from the extension ring is the right inclusion into
the tensor product. -/
private theorem objectRingCoord_canonicalMap {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') (x : C') :
    objectRingCoord G'
      (G'.canonicalMapToInvariantFunctions x : Γ(G'.groupoid.objects.left, ⊤)) =
    Algebra.TensorProduct.includeRight x := by
  show objectRingCoord G' ((Scheme.ΓSpecIso (.of C')).inv.hom x |> fun y =>
    (Scheme.Hom.appTop G'.groupoid.objects.hom).hom y) = _
  rw [← G'.objectsIso_over]
  show objectRingCoord G' ((Scheme.Hom.appTop G'.objectsIso.hom).hom
    ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C' →ₐ[invariantRing G]
        objectRingBaseChange G C').toRingHom))).hom
      ((Scheme.ΓSpecIso (.of C')).inv.hom x))) = _
  rw [objectRingCoord_appTop_objectsIso_hom]
  have hh := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (.of C')).inv.hom x))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C' →ₐ[invariantRing G]
        objectRingBaseChange G C').toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hh
  have hspec : (Scheme.ΓSpecIso (CommRingCat.of C')).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of C')).inv.hom x) = x := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      congrArg (fun k => k.hom x) (Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of C')))
  exact hh.trans (congrArg (fun z : C' =>
    (Algebra.TensorProduct.includeRight :
      C' →ₐ[invariantRing G] objectRingBaseChange G C') z) hspec)

/-- For a flat extension of the invariant ring, the canonical map from the extension ring to the
invariant functions of the base-changed groupoid scheme is bijective. -/
@[stacks 03BK "part (3), flat extensions of the invariant ring"]
theorem canonicalMapToInvariantFunctions_bijective_of_flat
    {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') :
    Function.Bijective G'.canonicalMapToInvariantFunctions := by
  classical
  let C := invariantRing G
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let : Algebra C B := invariantRingAlgebraArrow G
  let : Algebra C A := inferInstance
  let f := sourceAlgHom G
  let g := targetAlgHom G
  let fbase := Algebra.TensorProduct.map f (AlgHom.id C C')
  let gbase := Algebra.TensorProduct.map g (AlgHom.id C C')
  let E := fbase.equalizer gbase
  let ec : C →ₐ[C] f.equalizer g :=
    { toFun := fun c => ⟨c.1, by change sourceMap G c.1 = targetMap G c.1; exact c.2⟩
      map_one' := by ext; rfl
      map_mul' _ _ := by ext; rfl
      map_zero' := by ext; rfl
      map_add' _ _ := by ext; rfl
      commutes' := by intro c; ext; rfl }
  have hec : Function.Bijective ec :=
    ⟨fun x y h => Subtype.ext (congrArg Subtype.val h),
      fun x => ⟨⟨x.1, (x.2 : sourceMap G x.1 = targetMap G x.1)⟩, Subtype.ext rfl⟩⟩
  let ecore : C ≃ₐ[C] f.equalizer g := AlgEquiv.ofBijective ec hec
  have hmain := flat_tensor_equalizer_bijective (R := C) (S := C') (A := A) (B := B) f g ecore
  let objCoord := objectRingCoord G'
  let arrCoord := arrowRingCoord G'
  have hsrc : ∀ x : Γ(G'.groupoid.objects.left, ⊤),
      arrCoord (sourceMap G'.groupoid x) = fbase (objCoord x) :=
    arrowRingCoord_appTop_apply G' fbase.toRingHom _ G'.source_eq
  have htgt : ∀ x : Γ(G'.groupoid.objects.left, ⊤),
      arrCoord (targetMap G'.groupoid x) = gbase (objCoord x) :=
    arrowRingCoord_appTop_apply G' gbase.toRingHom _ G'.target_eq
  let invCoord : G'.invariantFunctions →+* E := RingHom.codRestrict
    (objCoord.toRingHom.comp (G'.invariantFunctions.subtype)) E (by
      intro x
      show fbase (objCoord x.1) = gbase (objCoord x.1)
      calc
        fbase (objCoord x.1) = arrCoord (sourceMap G'.groupoid x.1) := (hsrc x.1).symm
        _ = arrCoord (targetMap G'.groupoid x.1) := congrArg arrCoord x.2
        _ = gbase (objCoord x.1) := htgt x.1)
  have hinv : Function.Bijective invCoord := by
    constructor
    · intro x y h
      apply Subtype.val_injective
      apply objCoord.injective
      exact congrArg Subtype.val h
    · intro z
      let x : G'.invariantFunctions := ⟨objCoord.symm z, by
        show sourceMap G'.groupoid (objCoord.symm z) =
          targetMap G'.groupoid (objCoord.symm z)
        apply arrCoord.injective
        calc
          arrCoord (sourceMap G'.groupoid (objCoord.symm z)) = fbase z := by simp [hsrc]
          _ = gbase z := z.2
          _ = arrCoord (targetMap G'.groupoid (objCoord.symm z)) := by simp [htgt]⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      simp [invCoord, x]
  let eInv : G'.invariantFunctions ≃+* E := RingEquiv.ofBijective invCoord hinv
  have hfun : (fun x : C' => eInv (G'.canonicalMapToInvariantFunctions x)) =
      (fun x : C' => (⟨Algebra.TensorProduct.includeRight x,
        AlgHom.mem_equalizer fbase gbase _ |>.2 (by simp [fbase, gbase])⟩ : E)) := by
    funext x
    apply Subtype.ext
    simpa [eInv, invCoord, C] using objectRingCoord_canonicalMap G' x
  have hfinal :
      Function.Bijective (fun x : C' => eInv (G'.canonicalMapToInvariantFunctions x)) := by
    rw [hfun]
    exact hmain
  exact (eInv.bijective.of_comp_iff' _).mp hfinal

end AlgebraicGeometry
