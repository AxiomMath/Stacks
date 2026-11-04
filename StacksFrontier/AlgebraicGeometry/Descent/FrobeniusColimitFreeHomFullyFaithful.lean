module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFreeComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFreeHomSquare
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackHomSquare
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis

/-!
# Full faithfulness of the comparison functor of Stacks Tag 0EXD at free modules

Let `p` be a prime and let

```
E ⟶ X'
↓     ↓
Z ⟶ X
```

be a commutative square of schemes in characteristic `p`. The comparison functor
`AlgebraicGeometry.frobeniusColimitVectorBundlesComparison` into the categorical fibre product is
fully faithful exactly when, for every pair of objects, the square of its Hom-sets is cartesian
(`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`, which
carries no groupoid hypothesis). This file proves **that square is cartesian at every pair of
free modules**, given a cartesian square of global sections of the Frobenius colimits of the
structure sheaves.

Two inputs combine. The square of Hom-sets of free modules is cartesian when read through the
*naive* cospan of transition maps, by
`AlgebraicGeometry.isPullback_frobeniusColimitFreeHomRestrict_of_isPullback`; and the canonical
cospan which full faithfulness asks for, `g ↦ e^*g ≫ α` and `k ↦ α ≫ d^*k`, agrees with the
naive one under the free identifications, by
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_hom_app_hom_free`.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitFreeIsoComp`: **the free identification along a two-step
  route**, namely the transition of the free identification of the first step followed by the
  free identification of the second.

## Main results

* `AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_free`: **the two transition
  functors out of `X` are jointly injective on morphisms of free modules.** No comparison
  isomorphism enters: faithfulness does not mention it.
* `AlgebraicGeometry.exists_frobeniusColimitVectorBundles_free`: **every pair of morphisms of
  free modules over the centre and over the modification which agrees over the exceptional
  corner comes from a morphism over `X`.**
* `AlgebraicGeometry.isPullback_squareComparison_homSquare_free`: **the square of Hom-sets of the
  comparison functor is cartesian at a pair of free modules** — the hypothesis of
  `CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`,
  restricted to the free objects.
* `AlgebraicGeometry.isPullback_squareComparison_homSquare_free_twoGenerator`: the same at the
  almost blowup square of Stacks Example 0EVH, under exactly the hypotheses of that example, and
  `…_zmodTwo`: those hypotheses are inhabited, so the previous statement is not vacuously true.

## Implementation notes

**No `@[stacks 0EXD]` attribute appears in this file.** What Tag 0EXD asserts is that
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` is an equivalence. Full faithfulness
by the criterion above needs the cartesian Hom-square at *every* pair of objects of
`AlgebraicGeometry.frobeniusColimitVectorBundles (Spec A) p _`, and what is proved here is the
free pairs only; the passage to a general finite locally free module asks for the same square
over each member of a trivialising affine cover of `Spec A`. Essential surjectivity is not proved
here either.

The three results are stated for an arbitrary commutative square of schemes in characteristic
`p`, with the cartesian square of global sections as a hypothesis, so that nothing about almost
blowup squares enters; that hypothesis is discharged at the square of Example 0EVH by
`AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator`.

Faithfulness and the existence statement are proved from the cartesian square of Hom-sets by
`CategoryTheory.Limits.Types.ext_of_isPullback` and
`CategoryTheory.Limits.Types.exists_of_isPullback`, and the packaged cartesian square is then
reassembled from them and the naturality of the comparison isomorphism
(`CategoryTheory.Limits.CategoricalPullback.squareComparison_homSquare_w`) through
`CategoryTheory.Limits.Types.isPullback_iff`. Going through the elementary characterisation
rather than transporting along four isomorphisms of Hom-sets avoids having to produce the four
commutativity squares, two of which would need the comparison isomorphism's compatibility at
both index types anyway.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius Stacks.AlmostBlowUp TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **The free identification along a two-step route.** Extension of scalars along the transition
of `g` carries the free module to a free module, and extension of scalars along the transition of
`f` carries that one to a free module again; this is the composite identification. -/
noncomputable def frobeniusColimitFreeIsoComp {V W Y : Scheme.{u}} (f : V ⟶ W) (g : W ⟶ Y)
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p)
    (hY : IsInCharacteristic Y p) (I : Type u) :
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hV hW)).obj
        ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p g hW hY)).obj
            (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) I)) ≅
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf V p hV) I :=
  (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p f hV hW)).mapIso
      (_root_.SheafOfModules.pullbackObjFreeIso
        (frobeniusColimitStructureSheafHom p g hW hY) I) ≪≫
    _root_.SheafOfModules.pullbackObjFreeIso (frobeniusColimitStructureSheafHom p f hV hW) I

/-- The transition map on Hom-sets of free modules, written out: extension of scalars conjugated
by the free identifications at the two index types. -/
theorem frobeniusColimitFreeHomRestrict_apply {V W : Scheme.{u}} (f : V ⟶ W)
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p) (I L : Type u)
    (m : _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf W p hW) I ⟶
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf W p hW) L) :
    frobeniusColimitFreeHomRestrict p f hV hW I L m =
      (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p f hV hW) I).inv ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p f hV hW)).map m ≫
        (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p f hV hW) L).hom := rfl

/-- The transition map on Hom-sets of free modules, applied to a morphism of extensions of
scalars conjugated by the free identifications of the first step, is extension of scalars
conjugated by the free identifications of the two-step route. -/
theorem frobeniusColimitFreeHomRestrict_conj {V W Y : Scheme.{u}} (f : V ⟶ W) (g : W ⟶ Y)
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p)
    (hY : IsInCharacteristic Y p) (I L : Type u)
    (n : (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p g hW hY)).obj
            (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) I) ⟶
      (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p g hW hY)).obj
            (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) L)) :
    frobeniusColimitFreeHomRestrict p f hV hW I L
        ((_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p g hW hY) I).inv ≫ n ≫
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p g hW hY) L).hom) =
      (frobeniusColimitFreeIsoComp p f g hV hW hY I).inv ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p f hV hW)).map n ≫
        (frobeniusColimitFreeIsoComp p f g hV hW hY L).hom := by
  rw [frobeniusColimitFreeHomRestrict_apply]
  simp [frobeniusColimitFreeIsoComp]

/-- A morphism of free modules whose transition image is the conjugate of `n` by the free
identifications has extension of scalars equal to `n`. -/
private theorem pullback_map_eq_of_freeHomRestrict_eq {V W : Scheme.{u}} (f : V ⟶ W)
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p) (I L : Type u)
    (m : _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf W p hW) I ⟶
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf W p hW) L)
    (n : (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p f hV hW)).obj
            (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf W p hW) I) ⟶
      (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p f hV hW)).obj
            (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf W p hW) L))
    (h : frobeniusColimitFreeHomRestrict p f hV hW I L m =
      (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p f hV hW) I).inv ≫ n ≫
        (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p f hV hW) L).hom) :
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hV hW)).map m =
      n := by
  rw [frobeniusColimitFreeHomRestrict_apply] at h
  simpa using congrArg (fun t => (_root_.SheafOfModules.pullbackObjFreeIso
      (frobeniusColimitStructureSheafHom p f hV hW) I).hom ≫ t ≫
    (_root_.SheafOfModules.pullbackObjFreeIso
      (frobeniusColimitStructureSheafHom p f hV hW) L).inv) h

/-- The transition map on Hom-sets of free modules, applied to the underlying morphism of a
morphism of free objects of the category of finite locally free modules, is the underlying
morphism of its image under the transition functor, conjugated by the free identifications. -/
theorem frobeniusColimitFreeHomRestrict_hom {V Y : Scheme.{u}} (f : V ⟶ Y)
    (hV : IsInCharacteristic V p) (hY : IsInCharacteristic Y p) (I L : Type u)
    (hI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) I))
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) L))
    (m : (⟨_root_.SheafOfModules.free I, hI⟩ : frobeniusColimitVectorBundles Y p hY) ⟶
      ⟨_root_.SheafOfModules.free L, hL⟩) :
    frobeniusColimitFreeHomRestrict p f hV hY I L m.hom =
      (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p f hV hY) I).inv ≫
        ((frobeniusColimitVectorBundlesPullback p f hV hY).map m).hom ≫
        (_root_.SheafOfModules.pullbackObjFreeIso
          (frobeniusColimitStructureSheafHom p f hV hY) L).hom := rfl

/-- **A free module on a type with `r` elements is finite locally free**, so that it is an object
of the category of finite locally free modules over the Frobenius colimit. -/
theorem isFiniteLocallyFree_free_ulift (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX)
        (ULift.{u} (Fin r))) :=
  have := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free
    (R := frobeniusColimitRingSheaf X p hX) r
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r

/-- **The free object of rank `r`** of the category of finite locally free modules over the
Frobenius colimit of the structure sheaf. Naming it keeps a concrete instantiation small: the
anonymous pair of a free module and its finite local freeness forces the kernel to unfold the
Frobenius colimit at every occurrence, which a constant does not. -/
noncomputable def frobeniusColimitFreeVect (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (r : ℕ) : frobeniusColimitVectorBundles X p hX :=
  ⟨_root_.SheafOfModules.free (ULift.{u} (Fin r)), isFiniteLocallyFree_free_ulift X p hX r⟩

section Square

variable {X X' Z E : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_hom_app_hom_free` with the two
composite free identifications named. -/
theorem frobeniusColimitVectorBundlesSquareIso_hom_app_free_comp (hw : q ≫ b = e ≫ z)
    (I : Type u)
    (hI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I)) :
    ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
          ⟨_root_.SheafOfModules.free I, hI⟩).hom ≫
        (frobeniusColimitFreeIsoComp p q b hE hX' hX I).hom =
      (frobeniusColimitFreeIsoComp p e z hE hZ hX I).hom :=
  frobeniusColimitVectorBundlesSquareIso_hom_app_hom_free p b z q e hX hX' hZ hE hw I hI

variable (I L : Type u) [Finite L]
  (hI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I))
  (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L))
  (hsec : IsPullback (frobeniusColimitSectionsRestrictHom p z hZ hX)
    (frobeniusColimitSectionsRestrictHom p b hX' hX)
    (frobeniusColimitSectionsRestrictHom p e hE hZ)
    (frobeniusColimitSectionsRestrictHom p q hE hX'))

include hsec

/-- **The two transition functors out of `X` are jointly injective on morphisms of free
modules**: two morphisms of free `colim_F 𝒪_X`-modules which agree after restriction to the
centre and after restriction to the modification are equal. This is the faithfulness half, and
no comparison isomorphism enters it. -/
theorem jointly_injective_frobeniusColimitVectorBundles_free
    (f g : (⟨_root_.SheafOfModules.free I, hI⟩ : frobeniusColimitVectorBundles X p hX) ⟶
      ⟨_root_.SheafOfModules.free L, hL⟩)
    (h₁ : (frobeniusColimitVectorBundlesPullback p z hZ hX).map f =
      (frobeniusColimitVectorBundlesPullback p z hZ hX).map g)
    (h₂ : (frobeniusColimitVectorBundlesPullback p b hX' hX).map f =
      (frobeniusColimitVectorBundlesPullback p b hX' hX).map g) : f = g := by
  apply ObjectProperty.hom_ext
  refine Types.ext_of_isPullback
    (isPullback_frobeniusColimitFreeHomRestrict_of_isPullback p b z q e hX hX' hZ hE I L hsec)
    ?_ ?_
  · rw [frobeniusColimitFreeHomRestrict_hom p z hZ hX I L hI hL f,
      frobeniusColimitFreeHomRestrict_hom p z hZ hX I L hI hL g, h₁]
  · rw [frobeniusColimitFreeHomRestrict_hom p b hX' hX I L hI hL f,
      frobeniusColimitFreeHomRestrict_hom p b hX' hX I L hI hL g, h₂]

/-- **Every compatible pair of morphisms of free modules comes from a morphism over `X`**: a
morphism of free `colim_F 𝒪_Z`-modules and a morphism of free `colim_F 𝒪_{X'}`-modules whose
restrictions to the exceptional corner agree, through the comparison isomorphism, are the
restrictions of a single morphism of free `colim_F 𝒪_X`-modules. This is the fullness half. -/
theorem exists_frobeniusColimitVectorBundles_free (hw : q ≫ b = e ≫ z)
    (g : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj
        ⟨_root_.SheafOfModules.free I, hI⟩ ⟶
      (frobeniusColimitVectorBundlesPullback p z hZ hX).obj
        ⟨_root_.SheafOfModules.free L, hL⟩)
    (k : (frobeniusColimitVectorBundlesPullback p b hX' hX).obj
        ⟨_root_.SheafOfModules.free I, hI⟩ ⟶
      (frobeniusColimitVectorBundlesPullback p b hX' hX).obj
        ⟨_root_.SheafOfModules.free L, hL⟩)
    (w : (frobeniusColimitVectorBundlesPullback p e hE hZ).map g ≫
        (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
          ⟨_root_.SheafOfModules.free L, hL⟩ =
      (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
          ⟨_root_.SheafOfModules.free I, hI⟩ ≫
        (frobeniusColimitVectorBundlesPullback p q hE hX').map k) :
    ∃ f : (⟨_root_.SheafOfModules.free I, hI⟩ :
        frobeniusColimitVectorBundles X p hX) ⟶ ⟨_root_.SheafOfModules.free L, hL⟩,
      (frobeniusColimitVectorBundlesPullback p z hZ hX).map f = g ∧
        (frobeniusColimitVectorBundlesPullback p b hX' hX).map f = k := by
  obtain ⟨gp, hgp⟩ : ∃ gp : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p z hZ hX)).obj
          (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I) ⟶
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p z hZ hX)).obj
          (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L),
      gp = g.hom := ⟨g.hom, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ kp : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p b hX' hX)).obj
          (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I) ⟶
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p b hX' hX)).obj
          (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L),
      kp = k.hom := ⟨k.hom, rfl⟩
  obtain ⟨aI, haI⟩ : ∃ aI : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p e hE hZ)).obj
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p z hZ hX)).obj
              (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I)) ⟶
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p q hE hX')).obj
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p b hX' hX)).obj
              (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I)),
      aI = ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
        ⟨_root_.SheafOfModules.free I, hI⟩).hom := ⟨_, rfl⟩
  obtain ⟨aL, haL⟩ : ∃ aL : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p e hE hZ)).obj
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p z hZ hX)).obj
              (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L)) ⟶
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p q hE hX')).obj
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p b hX' hX)).obj
              (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L)),
      aL = ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
        ⟨_root_.SheafOfModules.free L, hL⟩).hom := ⟨_, rfl⟩
  have cI : aI ≫ (frobeniusColimitFreeIsoComp p q b hE hX' hX I).hom =
      (frobeniusColimitFreeIsoComp p e z hE hZ hX I).hom := by
    rw [haI]
    exact frobeniusColimitVectorBundlesSquareIso_hom_app_free_comp
      p b z q e hX hX' hZ hE hw I hI
  have cL : aL ≫ (frobeniusColimitFreeIsoComp p q b hE hX' hX L).hom =
      (frobeniusColimitFreeIsoComp p e z hE hZ hX L).hom := by
    rw [haL]
    exact frobeniusColimitVectorBundlesSquareIso_hom_app_free_comp
      p b z q e hX hX' hZ hE hw L hL
  have hw' : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p e hE hZ)).map gp ≫ aL =
      aI ≫ (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p q hE hX')).map kp := by
    rw [haI, haL, hgp, hkp]
    exact (ObjectProperty.ι _).congr_map w
  have hpb : frobeniusColimitFreeHomRestrict p e hE hZ I L
        ((_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p z hZ hX) I).inv ≫ gp ≫
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p z hZ hX) L).hom) =
      frobeniusColimitFreeHomRestrict p q hE hX' I L
        ((_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p b hX' hX) I).inv ≫ kp ≫
          (_root_.SheafOfModules.pullbackObjFreeIso
            (frobeniusColimitStructureSheafHom p b hX' hX) L).hom) := by
    rw [frobeniusColimitFreeHomRestrict_conj p e z hE hZ hX I L,
      frobeniusColimitFreeHomRestrict_conj p q b hE hX' hX I L, Iso.inv_comp_eq, ← cI]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← cL, reassoc_of% hw']
  obtain ⟨m, hm₁, hm₂⟩ := Types.exists_of_isPullback
    (isPullback_frobeniusColimitFreeHomRestrict_of_isPullback p b z q e hX hX' hZ hE I L hsec)
    _ _ hpb
  refine ⟨(ObjectProperty.homMk m : (⟨_root_.SheafOfModules.free I, hI⟩ :
    frobeniusColimitVectorBundles X p hX) ⟶ ⟨_root_.SheafOfModules.free L, hL⟩), ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    rw [← hgp]
    exact pullback_map_eq_of_freeHomRestrict_eq p z hZ hX I L m gp hm₁
  · apply ObjectProperty.hom_ext
    rw [← hkp]
    exact pullback_map_eq_of_freeHomRestrict_eq p b hX' hX I L m kp hm₂

/-- **The square of Hom-sets of the comparison functor is cartesian at a pair of free modules.**
This is the hypothesis of
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`,
restricted to the free objects: commutativity is the naturality of the comparison isomorphism,
joint injectivity is
`AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_free` and the existence
statement is `AlgebraicGeometry.exists_frobeniusColimitVectorBundles_free`. -/
theorem isPullback_squareComparison_homSquare_free (hw : q ≫ b = e ≫ z) :
    IsPullback
      (↾fun f : (⟨_root_.SheafOfModules.free I, hI⟩ :
            frobeniusColimitVectorBundles X p hX) ⟶ ⟨_root_.SheafOfModules.free L, hL⟩ =>
        (frobeniusColimitVectorBundlesPullback p z hZ hX).map f)
      (↾fun f : (⟨_root_.SheafOfModules.free I, hI⟩ :
            frobeniusColimitVectorBundles X p hX) ⟶ ⟨_root_.SheafOfModules.free L, hL⟩ =>
        (frobeniusColimitVectorBundlesPullback p b hX' hX).map f)
      (↾fun gg : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj
            ⟨_root_.SheafOfModules.free I, hI⟩ ⟶
          (frobeniusColimitVectorBundlesPullback p z hZ hX).obj
            ⟨_root_.SheafOfModules.free L, hL⟩ =>
        (frobeniusColimitVectorBundlesPullback p e hE hZ).map gg ≫
          (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
            ⟨_root_.SheafOfModules.free L, hL⟩)
      (↾fun kk : (frobeniusColimitVectorBundlesPullback p b hX' hX).obj
            ⟨_root_.SheafOfModules.free I, hI⟩ ⟶
          (frobeniusColimitVectorBundlesPullback p b hX' hX).obj
            ⟨_root_.SheafOfModules.free L, hL⟩ =>
        (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
            ⟨_root_.SheafOfModules.free I, hI⟩ ≫
          (frobeniusColimitVectorBundlesPullback p q hE hX').map kk) := by
  rw [Types.isPullback_iff]
  refine ⟨CategoryTheory.Limits.CategoricalPullback.squareComparison_homSquare_w
      (frobeniusColimitVectorBundlesPullback p z hZ hX)
      (frobeniusColimitVectorBundlesPullback p b hX' hX)
      (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')
      (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw) _ _, ?_, ?_⟩
  · exact fun f₁ f₂ h => jointly_injective_frobeniusColimitVectorBundles_free p b z q e hX hX' hZ
      hE I L hI hL hsec f₁ f₂ h.1 h.2
  · exact fun gg kk hgk => exists_frobeniusColimitVectorBundles_free p b z q e hX hX' hZ hE I L
      hI hL hsec hw gg kk hgk

/-- **The square of Hom-sets of the comparison functor is cartesian at a pair of free objects of
finite rank.** This is
`AlgebraicGeometry.isPullback_squareComparison_homSquare_free` read at
`AlgebraicGeometry.frobeniusColimitFreeVect`. -/
theorem isPullback_squareComparison_homSquare_freeVect (hw : q ≫ b = e ≫ z) (r s : ℕ) :
    IsPullback
      (↾fun f : frobeniusColimitFreeVect X p hX r ⟶
          frobeniusColimitFreeVect X p hX s =>
        (frobeniusColimitVectorBundlesPullback p z hZ hX).map f)
      (↾fun f : frobeniusColimitFreeVect X p hX r ⟶
          frobeniusColimitFreeVect X p hX s =>
        (frobeniusColimitVectorBundlesPullback p b hX' hX).map f)
      (↾fun gg : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj
            (frobeniusColimitFreeVect X p hX r) ⟶
          (frobeniusColimitVectorBundlesPullback p z hZ hX).obj (frobeniusColimitFreeVect X p hX s)
            =>
        (frobeniusColimitVectorBundlesPullback p e hE hZ).map gg ≫
          (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
            (frobeniusColimitFreeVect X p hX s))
      (↾fun kk : (frobeniusColimitVectorBundlesPullback p b hX' hX).obj
            (frobeniusColimitFreeVect X p hX r) ⟶
          (frobeniusColimitVectorBundlesPullback p b hX' hX).obj (frobeniusColimitFreeVect X p hX
            s) =>
        (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
          (frobeniusColimitFreeVect X p hX r) ≫
          (frobeniusColimitVectorBundlesPullback p q hE hX').map kk) :=
  isPullback_squareComparison_homSquare_free p b z q e hX hX' hZ hE
    (ULift.{u} (Fin r)) (ULift.{u} (Fin s))
    (isFiniteLocallyFree_free_ulift X p hX r) (isFiniteLocallyFree_free_ulift X p hX s) hsec hw

end Square

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The square of Hom-sets of the comparison functor of Stacks Tag 0EXD is cartesian at a pair
of free modules of finite rank**, for the almost blowup square of Stacks Example 0EVH, under
exactly the hypotheses of that example: a ring `A`, two elements of it, and a prime `p` which
vanishes in `A`.

This is the full faithfulness of `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` at
*free* modules. It is not the tag: full faithfulness by
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback` needs
the same square at every pair of finite locally free modules, and essential surjectivity is a
separate matter. -/
theorem isPullback_squareComparison_homSquare_free_twoGenerator (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0) (r s : ℕ) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsPullback
      (↾fun f : frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA) r ⟶
          frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA) s =>
        (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA) (isInCharacteristic_spec A p
            hpA)).map f)
      (↾fun f : frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA) r ⟶
          frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA) s =>
        (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA) (isInCharacteristic_spec A p
            hpA)).map f)
      (↾fun gg : (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA) (isInCharacteristic_spec A p
            hpA)).obj
            (frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA) r) ⟶
          (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA) (isInCharacteristic_spec A p
            hpA)).obj (frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA)
              s) =>
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)).map gg ≫
          (frobeniusColimitVectorBundlesSquareIso p (modificationToBase A f₁ f₂)
          (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
          (exceptionalToCenter A f₁ f₂) (isInCharacteristic_spec A p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (twoGenerator_isPullback A f₁ f₂).w).hom.app (frobeniusColimitFreeVect (Spec (.of A)) p
            (isInCharacteristic_spec A p hpA) s))
      (↾fun kk : (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA) (isInCharacteristic_spec A p
            hpA)).obj
            (frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA) r) ⟶
          (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA) (isInCharacteristic_spec A p
            hpA)).obj (frobeniusColimitFreeVect (Spec (.of A)) p (isInCharacteristic_spec A p hpA)
              s) =>
        (frobeniusColimitVectorBundlesSquareIso p (modificationToBase A f₁ f₂)
          (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
          (exceptionalToCenter A f₁ f₂) (isInCharacteristic_spec A p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (twoGenerator_isPullback A f₁ f₂).w).hom.app (frobeniusColimitFreeVect (Spec (.of A)) p
            (isInCharacteristic_spec A p hpA) r) ≫
          (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)).map kk) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  exact isPullback_squareComparison_homSquare_freeVect p (modificationToBase A f₁ f₂)
    (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
    (isInCharacteristic_spec A p hpA) (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    (isPullback_frobeniusColimitSections_twoGenerator p hp A f₁ f₂ hpA)
    (twoGenerator_isPullback A f₁ f₂).w r s

/-- **The hypotheses of the previous theorem are inhabited**, so that it is not vacuously true:
they hold for `A = ZMod 2`, `f₁ = f₂ = 0` and `p = 2`, at free modules of rank one. -/
theorem isPullback_squareComparison_homSquare_free_twoGenerator_zmodTwo :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI := (twoGeneratorSquare (ZMod 2) 0 0).modificationGraded
    IsPullback
      (↾fun f : frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2)
        2 (ZMod.natCast_self 2)) 1 ⟶
          frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2
            (ZMod.natCast_self 2)) 1 =>
        (frobeniusColimitVectorBundlesPullback 2 (centerToBase (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
            (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2))).map f)
      (↾fun f : frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2)
        2 (ZMod.natCast_self 2)) 1 ⟶
          frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2
            (ZMod.natCast_self 2)) 1 =>
        (frobeniusColimitVectorBundlesPullback 2 (modificationToBase (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
            (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2))).map f)
      (↾fun gg : (frobeniusColimitVectorBundlesPullback 2 (centerToBase (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
            (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2))).obj
            (frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2
              (ZMod.natCast_self 2)) 1) ⟶
          (frobeniusColimitVectorBundlesPullback 2 (centerToBase (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
            (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2))).obj
              (frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2
                (ZMod.natCast_self 2)) 1) =>
        (frobeniusColimitVectorBundlesPullback 2 (exceptionalToCenter (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorExceptional (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (ZMod.natCast_self 2))).map gg ≫
          (frobeniusColimitVectorBundlesSquareIso 2 (modificationToBase (ZMod 2) 0 0)
          (centerToBase (ZMod 2) 0 0) (exceptionalToModification (ZMod 2) 0 0)
          (exceptionalToCenter (ZMod 2) 0 0) (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self
            2))
          (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (isInCharacteristic_twoGeneratorExceptional (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (twoGenerator_isPullback (ZMod 2) 0 0).w).hom.app (frobeniusColimitFreeVect (Spec (.of
            (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2)) 1))
      (↾fun kk : (frobeniusColimitVectorBundlesPullback 2 (modificationToBase (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
            (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2))).obj
            (frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2
              (ZMod.natCast_self 2)) 1) ⟶
          (frobeniusColimitVectorBundlesPullback 2 (modificationToBase (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
            (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2))).obj
              (frobeniusColimitFreeVect (Spec (.of (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2
                (ZMod.natCast_self 2)) 1) =>
        (frobeniusColimitVectorBundlesSquareIso 2 (modificationToBase (ZMod 2) 0 0)
          (centerToBase (ZMod 2) 0 0) (exceptionalToModification (ZMod 2) 0 0)
          (exceptionalToCenter (ZMod 2) 0 0) (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self
            2))
          (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (isInCharacteristic_twoGeneratorExceptional (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (twoGenerator_isPullback (ZMod 2) 0 0).w).hom.app (frobeniusColimitFreeVect (Spec (.of
            (ZMod 2))) 2 (isInCharacteristic_spec (ZMod 2) 2 (ZMod.natCast_self 2)) 1) ≫
          (frobeniusColimitVectorBundlesPullback 2 (exceptionalToModification (ZMod 2) 0 0)
          (isInCharacteristic_twoGeneratorExceptional (ZMod 2) 0 0 2 (ZMod.natCast_self 2))
          (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (ZMod.natCast_self 2))).map
            kk) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := (twoGeneratorSquare (ZMod 2) 0 0).modificationGraded
  exact isPullback_squareComparison_homSquare_free_twoGenerator 2 Nat.prime_two (ZMod 2) 0 0
    (ZMod.natCast_self 2) 1 1

end AlgebraicGeometry

end
