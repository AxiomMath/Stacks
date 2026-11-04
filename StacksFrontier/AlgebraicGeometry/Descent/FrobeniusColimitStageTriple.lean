module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitHomReduction
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitIsoLevel
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullback

/-!
# A triple of `colim_F`-modules descends to a triple of modules at one Frobenius stage

Let `p` be a prime and let

```
E ⟶ X'
↓    ↓
Z ⟶ X
```

be a commutative square of schemes in characteristic `p`.  The essential surjectivity half of
[Stacks, Tag 0EXD] starts from an object of the categorical fibre product

`Vect(colim_F 𝒪_Z) ×_{Vect(colim_F 𝒪_E)} Vect(colim_F 𝒪_{X'})`

— a finite locally free `colim_F 𝒪_Z`-module, a finite locally free `colim_F 𝒪_{X'}`-module and
an isomorphism of their transitions to `E` — and has to replace it by a triple of **ordinary**
finite locally free modules, so that the Noetherian reduction of [Stacks, Tag 0B8W] and the
`ℐ`-adic induction can be applied to it.  The source performs that replacement in the sentence
"*we have to show that after replacing this triple by a Frobenius power pullback, it comes from a
finite locally free `𝒪_X`-module*".

Both modules come from a stage by [Stacks, Tag 0EXB]
(`AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso`), so the content of this file is the
**structural isomorphism**: nothing identified the isomorphism `φ` carried by an object of the
categorical fibre product with the comparison `φₙ` of the ordinary triple it descends to.  Two
things were missing and are supplied here.

* The transition functor of [Stacks, Tag 0EXE] commutes with the stage functors of
  [Stacks, Tag 0EXB]: `AlgebraicGeometry.frobeniusStageFunctorPullbackIso`.  Without it the
  conjugate of `φ` by the two descent isomorphisms is a morphism between transitions of stage
  images rather than between stage images of transitions, and the ordinary triple cannot even be
  *stated*.
* An isomorphism between two stage images is the stage image of an isomorphism of `𝒪_X`-modules
  at some Frobenius twist: `AlgebraicGeometry.exists_frobeniusStageIso_hom_eq`.  This is
  [Stacks, Tag 0EXA]'s description of the Hom-sets as filtered colimits, read through the
  equivalence of [Stacks, Tag 0EXB].

## Main definitions

* `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso`: **extension of scalars along a
  coprojection commutes with extension of scalars along the canonical morphism of Frobenius
  colimits**, on all sheaves of modules.
* `AlgebraicGeometry.frobeniusStageFunctorPullbackIso`: the same on the finite locally free
  modules — **the stage functor of [Stacks, Tag 0EXB] commutes with the transition functor of
  [Stacks, Tag 0EXE]**.
* `AlgebraicGeometry.frobeniusStageHomIso`: the isomorphism of stage images induced by an
  isomorphism of `𝒪_X`-modules at a Frobenius twist.
* `AlgebraicGeometry.frobeniusColimitStageTriple`: **the object of the categorical fibre product
  attached to a triple of ordinary modules**, namely two finite locally free modules on `Z` and
  on `X'` together with an isomorphism of the `j`-fold Frobenius pullbacks of their restrictions
  to `E`.

## Main results

* `AlgebraicGeometry.exists_frobeniusStageIso_hom_eq`: **an isomorphism between two stage images
  is presented by an isomorphism of `𝒪_X`-modules at some Frobenius twist.**
* `AlgebraicGeometry.exists_frobeniusColimitStageTriple_iso`: **every object of the categorical
  fibre product is isomorphic to one attached to a triple of ordinary modules**, the three
  corners being quasi-compact and quasi-separated.

## Implementation notes

The commutation of the stage functor with the transition functor is an instance of the
pseudofunctoriality of extension of scalars, and the one piece of content is the commutativity of
the square of sheaves of rings

```
𝒪_Y ⟶ colim_F 𝒪_Y
 ↓          ↓
f_*𝒪_X ⟶ f_*(colim_F 𝒪_X)
```

which is the stage formula
`AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitStructureSheafHom`.  Both composites
around the square are therefore extension of scalars along *one and the same* morphism of sheaves
of rings, so the comparison is Mathlib's `CategoryTheory.SheafOfModules.pullbackComp` at each
corner with an `eqToIso` between them; the two site functors
`Opens.map (𝟙 Y) ⋙ Opens.map f.base` and `Opens.map f.base ⋙ Opens.map (𝟙 X)` are the same
functor, so no transport across the sites is needed.

The structural isomorphism of `AlgebraicGeometry.frobeniusColimitStageTriple` is carried at a
Frobenius twist `j` rather than on the nose, and that is deliberate: it is what keeps the triple
at **one** stage `n`.  Lowering the twist to `0` would mean replacing the pair of modules by their
`j`-fold Frobenius pullbacks and the stage `n` by `n + j`, which is a different object of the
categorical fibre product, isomorphic to this one only through the compatibility of
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso` with
`AlgebraicGeometry.frobeniusStageFunctorIterIso`.  Carrying the twist costs nothing, since
`AlgebraicGeometry.frobeniusStageHomMap` turns a morphism at any twist into a morphism of the
stage images and is functorial there (`AlgebraicGeometry.frobeniusStageHomMap_comp` and
`AlgebraicGeometry.frobeniusStageHomMap_id`), which is exactly what makes
`AlgebraicGeometry.frobeniusStageHomIso` an isomorphism.

The descent of an isomorphism goes through the model `colim_F Vect(X)` of [Stacks, Tag 0EXA]:
the comparison functor of [Stacks, Tag 0EXB] is fully faithful unconditionally
(`AlgebraicGeometry.full_frobeniusColimitVectComparison` and
`AlgebraicGeometry.faithful_frobeniusColimitVectComparison`), so the isomorphism has a preimage
there, and `CategoryTheory.EndoColim.exists_iso_hom_eq` presents an isomorphism of the model by
an isomorphism of `C` at some level.  The preimage is taken of the isomorphism *retyped* at the
comparison functor's spelling of its source and target: that retyping is definitional, and
taking it first turns the unification `F.obj ?X ≅ F.obj ?Y` — which asks the elaborator to invert
the comparison functor on objects and times out at `whnf` — into a first-order one.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The stage functor commutes with the transition functor -/

section Bridge

variable {X Y : Scheme.{u}} (p : ℕ) [Fact p.Prime]

/-- **Extension of scalars along a coprojection commutes with extension of scalars along the
canonical morphism of Frobenius colimits**, on all sheaves of modules.  Both composites are
extension of scalars along the single morphism of sheaves of rings
`𝒪_Y ⟶ f_*(colim_F 𝒪_X)` of the stage formula
`AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitStructureSheafHom`. -/
noncomputable def frobeniusStageExtendScalarsPullbackIso (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ) :
    frobeniusStageExtendScalars Y p hY n ⋙
        _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY) ≅
      Scheme.Modules.pullback f ⋙ frobeniusStageExtendScalars X p hX n :=
  _root_.SheafOfModules.pullbackComp.{u} (frobeniusStageStructureMap Y p hY n)
      (frobeniusColimitStructureSheafHom p f hX hY) ≪≫
    eqToIso (congrArg (fun φ => _root_.SheafOfModules.pullback.{u} φ)
      (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY n)) ≪≫
    (_root_.SheafOfModules.pullbackComp.{u} f.ringSheafOnOpensHom
      (frobeniusStageStructureMap X p hX n)).symm

/-- **The stage functor of [Stacks, Tag 0EXB] commutes with the transition functor of
[Stacks, Tag 0EXE].**  Restricting a finite locally free `𝒪_Y`-module along `f` and then
extending scalars to `colim_F 𝒪_X` is extending scalars to `colim_F 𝒪_Y` and then transferring
along `f`.  Without this the structural isomorphism of an object of the categorical fibre
product of [Stacks, Tag 0EXD] cannot be compared with the comparison isomorphism of an ordinary
triple. -/
noncomputable def frobeniusStageFunctorPullbackIso (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ) :
    frobeniusStageFunctor Y p hY n ⋙ frobeniusColimitVectorBundlesPullback p f hX hY ≅
      Scheme.Vect.pullback f ⋙ frobeniusStageFunctor X p hX n :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _
      ((frobeniusStageExtendScalarsPullbackIso p f hX hY n).app E.1))
    (fun g ↦ (ObjectProperty.ι _).map_injective
      ((frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom.naturality g.hom))

end Bridge

/-! ### An isomorphism of stage images comes from a stage -/

section Descent

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **An object presented at stage `n` is presented at every later stage**, by
`AlgebraicGeometry.frobeniusStageFunctorIterIso`. -/
theorem exists_frobeniusStageFunctor_obj_iso_of_le (n m : ℕ) (h : n ≤ m) (E : X.Vect) :
    ∃ E' : X.Vect, Nonempty ((frobeniusStageFunctor X p hX m).obj E' ≅
      (frobeniusStageFunctor X p hX n).obj E) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨(frobeniusPullbackIter X p hX k).obj E,
    ⟨(frobeniusStageFunctorIterIso X p hX n k).app E⟩⟩

/-- **The isomorphism of stage images induced by an isomorphism of `𝒪_X`-modules at a Frobenius
twist.**  It is an isomorphism because `AlgebraicGeometry.frobeniusStageHomMap` at a fixed twist
is functorial. -/
noncomputable def frobeniusStageHomIso (n k : ℕ) {E G : X.Vect}
    (u : (frobeniusPullbackIter X p hX k).obj E ≅ (frobeniusPullbackIter X p hX k).obj G) :
    (frobeniusStageFunctor X p hX n).obj E ≅ (frobeniusStageFunctor X p hX n).obj G where
  hom := frobeniusStageHomMap X p hX n k u.hom
  inv := frobeniusStageHomMap X p hX n k u.inv
  hom_inv_id := by
    rw [frobeniusStageHomMap_comp, u.hom_inv_id, frobeniusStageHomMap_id]
  inv_hom_id := by
    rw [frobeniusStageHomMap_comp, u.inv_hom_id, frobeniusStageHomMap_id]

/-- **An isomorphism between two stage images is presented by an isomorphism of `𝒪_X`-modules at
some Frobenius twist.**  The comparison functor of [Stacks, Tag 0EXB] is fully faithful, so the
isomorphism has a preimage in the model `colim_F Vect(X)` of [Stacks, Tag 0EXA], and
`CategoryTheory.EndoColim.exists_iso_hom_eq` presents an isomorphism of the model by an
isomorphism of `Vect(X)`. -/
theorem exists_frobeniusStageIso_hom_eq [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (P Q : X.Vect)
    (ω : (frobeniusStageFunctor X p hX n).obj P ≅ (frobeniusStageFunctor X p hX n).obj Q) :
    ∃ (k : ℕ) (u : (frobeniusPullbackIter X p hX (n + k)).obj P ≅
        (frobeniusPullbackIter X p hX (n + k)).obj Q),
      frobeniusStageHomMap X p hX n (n + k) u.hom = ω.hom := by
  have := full_frobeniusColimitVectComparison X p hX
  have := faithful_frobeniusColimitVectComparison X p hX
  have key : ∀ ω' : (frobeniusColimitVectComparison X p hX).obj
        (⟨P, n⟩ : frobeniusColimitVectModel X p hX) ≅
      (frobeniusColimitVectComparison X p hX).obj
        (⟨Q, n⟩ : frobeniusColimitVectModel X p hX),
      ∃ (k : ℕ) (u : (frobeniusPullbackIter X p hX (n + k)).obj P ≅
          (frobeniusPullbackIter X p hX (n + k)).obj Q),
        frobeniusStageHomMap X p hX n (n + k) u.hom = ω'.hom := by
    intro ω'
    have hv : (frobeniusColimitVectComparison X p hX).map
        ((frobeniusColimitVectComparison X p hX).preimageIso ω').hom = ω'.hom :=
      (frobeniusColimitVectComparison X p hX).map_preimage ω'.hom
    obtain ⟨k, u, hu⟩ := EndoColim.exists_iso_hom_eq
      ((frobeniusColimitVectComparison X p hX).preimageIso ω')
    have h1 : (frobeniusColimitVectComparison X p hX).map
        (EndoColim.Hom.of k u.hom :
          (⟨P, n⟩ : frobeniusColimitVectModel X p hX) ⟶ ⟨Q, n⟩)
        = frobeniusStageHomMap X p hX n (n + k) u.hom :=
      frobeniusColimitVectComparison_map_of X p hX n k u.hom
    exact ⟨k, u,
      h1.symm.trans ((congrArg (frobeniusColimitVectComparison X p hX).map hu).trans hv)⟩
  exact key ω

end Descent

/-! ### The triple of ordinary modules an object of the fibre product descends to -/

section Triple

variable {XZ XM XE : Scheme.{u}} (p : ℕ) [Fact p.Prime]
  (e : XE ⟶ XZ) (d : XE ⟶ XM)
  (hZ : IsInCharacteristic XZ p) (hM : IsInCharacteristic XM p)
  (hE : IsInCharacteristic XE p)

/-- **The object of the categorical fibre product attached to a triple of ordinary modules.**
The triple is a finite locally free `𝒪_Z`-module `Ec`, a finite locally free `𝒪_{X'}`-module `Em`
and an isomorphism `psi` of the `j`-fold Frobenius pullbacks of their restrictions to `E`; the
structural isomorphism of the object is `psi`, read on the stage-`n` images through
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso` at the two legs of the cospan. -/
noncomputable def frobeniusColimitStageTriple (n j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
    (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
      (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)) :
    CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p d hE hM) where
  fst := (frobeniusStageFunctor XZ p hZ n).obj Ec
  snd := (frobeniusStageFunctor XM p hM n).obj Em
  iso := (frobeniusStageFunctorPullbackIso p e hE hZ n).app Ec ≪≫
    frobeniusStageHomIso XE p hE n j psi ≪≫
    ((frobeniusStageFunctorPullbackIso p d hE hM n).app Em).symm

/-- The first component of `AlgebraicGeometry.frobeniusColimitStageTriple` is the stage-`n`
image of `Ec`. -/
@[simp]
lemma frobeniusColimitStageTriple_fst (n j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
    (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
      (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)) :
    (frobeniusColimitStageTriple p e d hZ hM hE n j Ec Em psi).fst =
      (frobeniusStageFunctor XZ p hZ n).obj Ec := rfl

/-- The second component of `AlgebraicGeometry.frobeniusColimitStageTriple` is the stage-`n`
image of `Em`. -/
@[simp]
lemma frobeniusColimitStageTriple_snd (n j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
    (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
      (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)) :
    (frobeniusColimitStageTriple p e d hZ hM hE n j Ec Em psi).snd =
      (frobeniusStageFunctor XM p hM n).obj Em := rfl

/-- The structural isomorphism of `AlgebraicGeometry.frobeniusColimitStageTriple`, with
`AlgebraicGeometry.frobeniusStageHomIso` unfolded to
`AlgebraicGeometry.frobeniusStageHomMap`. -/
lemma frobeniusColimitStageTriple_iso_hom (n j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
    (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
      (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)) :
    (frobeniusColimitStageTriple p e d hZ hM hE n j Ec Em psi).iso.hom =
      ((frobeniusStageFunctorPullbackIso p e hE hZ n).app Ec).hom ≫
        frobeniusStageHomMap XE p hE n j psi.hom ≫
        ((frobeniusStageFunctorPullbackIso p d hE hM n).app Em).inv := rfl

/-- **Every object of the categorical fibre product of [Stacks, Tag 0EXD] is isomorphic to one
attached to a triple of ordinary finite locally free modules.**

The two modules come from a stage by [Stacks, Tag 0EXB], and are brought to one and the same
stage by `AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso_of_le`.  The structural
isomorphism, conjugated by the two descent isomorphisms and carried across the cospan by
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso`, is an isomorphism between two stage images
over `E`, hence is presented by an isomorphism of `𝒪_E`-modules at some Frobenius twist by
`AlgebraicGeometry.exists_frobeniusStageIso_hom_eq`.  That isomorphism is the `psi` of the
triple, and the compatibility the categorical fibre product asks for holds by construction. -/
theorem exists_frobeniusColimitStageTriple_iso
    [CompactSpace XZ] [QuasiSeparatedSpace XZ] [CompactSpace XM] [QuasiSeparatedSpace XM]
    [CompactSpace XE] [QuasiSeparatedSpace XE]
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p d hE hM)) :
    ∃ (n j : ℕ) (Ec : XZ.Vect) (Em : XM.Vect)
      (psi : (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback e).obj Ec) ≅
        (frobeniusPullbackIter XE p hE j).obj ((Scheme.Vect.pullback d).obj Em)),
      Nonempty (T ≅ frobeniusColimitStageTriple p e d hZ hM hE n j Ec Em psi) := by
  obtain ⟨n₁, Ec₁, ⟨ic₁⟩⟩ := exists_frobeniusStageFunctor_obj_iso XZ p hZ T.fst
  obtain ⟨n₂, Em₂, ⟨im₂⟩⟩ := exists_frobeniusStageFunctor_obj_iso XM p hM T.snd
  obtain ⟨Ec, ⟨ec⟩⟩ := exists_frobeniusStageFunctor_obj_iso_of_le XZ p hZ n₁ (max n₁ n₂)
    (le_max_left _ _) Ec₁
  obtain ⟨Em, ⟨em⟩⟩ := exists_frobeniusStageFunctor_obj_iso_of_le XM p hM n₂ (max n₁ n₂)
    (le_max_right _ _) Em₂
  obtain ⟨k, u, hu⟩ := exists_frobeniusStageIso_hom_eq XE p hE (max n₁ n₂)
    ((Scheme.Vect.pullback e).obj Ec) ((Scheme.Vect.pullback d).obj Em)
    (((frobeniusStageFunctorPullbackIso p e hE hZ (max n₁ n₂)).app Ec).symm ≪≫
      ((frobeniusColimitVectorBundlesPullback p e hE hZ).mapIso (ec ≪≫ ic₁) ≪≫ T.iso ≪≫
        ((frobeniusColimitVectorBundlesPullback p d hE hM).mapIso (em ≪≫ im₂)).symm) ≪≫
      ((frobeniusStageFunctorPullbackIso p d hE hM (max n₁ n₂)).app Em))
  refine ⟨max n₁ n₂, max n₁ n₂ + k, Ec, Em, u,
    ⟨CategoricalPullback.mkIso (ec ≪≫ ic₁).symm (em ≪≫ im₂).symm ?_⟩⟩
  rw [frobeniusColimitStageTriple_iso_hom, hu]
  simp

end Triple

end AlgebraicGeometry

end
