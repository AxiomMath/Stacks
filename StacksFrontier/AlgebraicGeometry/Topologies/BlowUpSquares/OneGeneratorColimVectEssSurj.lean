module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitIsoLevel
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.OneGeneratorVectGlue
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectFull
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectFullFunctor

/-!
# Towards essential surjectivity of the comparison of Stacks Tag 0EXC

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be an
ideal annihilated by `f ^ n`, so that the spectra of

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

form the almost blowup square of More on Flatness, Example 0EVG. The comparison functor of
Stacks Tag 0EXC

`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`

is `AlgebraicGeometry.colimVectComparison`; it is faithful by
`AlgebraicGeometry.colimVectComparison_faithful`. This file assembles three of the four steps of
the *essential surjectivity* of that functor.

At the near end, an object of the categorical pullback is a pair of objects of the two colimit
categories together with an isomorphism of their images in the colimit category of the
exceptional corner, and none of the three is given at a finite stage. Both objects are moved to
one common stage by the isomorphisms `(ℰ, n) ≅ (F^{k,*}ℰ, n + k)` of Stacks Tag 0EXA, and the
isomorphism between their images is then presented at a finite level by an honest isomorphism of
vector bundles on the exceptional corner — the content of
`AlgebraicGeometry.exists_presented_compatible_pair`.

The triple so obtained is a compatible pair of vector bundles over the exceptional corner, and
`AlgebraicGeometry.exists_finProj_of_vect_pair` identifies it with the image of a finite
projective `A ⧸ (J ∩ fA)`-module under the canonical comparison of Stacks Tag 0D2J. The
identification is an isomorphism *in the categorical pullback*, so it carries the compatibility
over the exceptional corner, which is what
`MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProj_obj` adds to the two separate
reduction isomorphisms of `AlgebraicGeometry.exists_vect_of_compatible_pair`. The transport of
the categorical pullback across the affine comparison is an instance of the general
construction `CategoryTheory.Limits.CategoricalPullback.mapCospan` and of its essential
surjectivity `CategoryTheory.Limits.CategoricalPullback.essSurj_mapCospan`.

At the far end, the vector bundle on `Spec A` which such a module `L` glues to is the
restriction of `L^~` along `Spec` of the Frobenius factorisation
`MilnorPatching.OneGeneratorFrobenius.betaHom`. Its two restrictions to the centre and to the
modification are computed here, as named isomorphisms onto the `N`-th Frobenius twists of the
two reductions of `L`.

## Main definitions

* `CategoryTheory.Limits.CategoricalPullback.mapCospan`: **the functor between categorical
  pullbacks induced by a transformation of cospans.**
* `AlgebraicGeometry.tildeCornerCospanTransform`: the affine comparison
  `AlgebraicGeometry.tildeVect` as a transformation of the cospan of extensions of scalars onto
  `A ⧸ (J + fA)` into the cospan of restrictions of vector bundles to the exceptional corner.
* `AlgebraicGeometry.OneGeneratorSquare.ctrCornerSquareIter` and
  `AlgebraicGeometry.OneGeneratorSquare.modCornerSquareIter`: the iterated Frobenius comparisons
  `F_E^{k,*}(ℰ|_E) ≅ (F_Z^{k,*}ℰ)|_E` on the two legs into the exceptional corner.
* `AlgebraicGeometry.OneGeneratorSquare.commonStageCentreIso` and
  `AlgebraicGeometry.OneGeneratorSquare.commonStageModificationIso`: **the two components of an
  object of the categorical pullback, moved to a common stage.**
* `AlgebraicGeometry.OneGeneratorSquare.betaGluedVect`: the vector bundle on `Spec A` which a
  finite projective `A ⧸ (J ∩ fA)`-module glues to, namely the restriction of `L^~` along `Spec`
  of the Frobenius factorisation.
* `AlgebraicGeometry.OneGeneratorSquare.betaGluedVectCentreIso` and
  `AlgebraicGeometry.OneGeneratorSquare.betaGluedVectModificationIso`: **the two restrictions of
  that vector bundle**, as the `N`-th Frobenius twists of the two reductions of `L`.
* `AlgebraicGeometry.OneGeneratorSquare.betaGluedVectCentreTwistIso` and
  `AlgebraicGeometry.OneGeneratorSquare.betaGluedVectModificationTwistIso`: the same two
  isomorphisms with the Frobenius twist spelled as an iterate of
  `AlgebraicGeometry.frobeniusPullback`, which is the form the colimit category consumes.

## Main results

* `AlgebraicGeometry.exists_presented_compatible_pair`: **an object of the categorical pullback
  of Stacks Tag 0EXC is isomorphic to a pair of vector bundles placed at one common stage
  together with an isomorphism of their restrictions to the exceptional corner, presented at a
  finite level.** This is the reduction of the essential surjectivity of the comparison functor
  to the object-level gluing problem on vector bundles.
* `CategoryTheory.Limits.CategoricalPullback.essSurj_mapCospan`: the induced functor between
  categorical pullbacks is essentially surjective as soon as the two outer functors of the
  transformation are and the middle one is fully faithful.
* `AlgebraicGeometry.exists_finProj_of_vect_pair`: **a compatible pair of vector bundles over
  the exceptional corner comes from a finite projective `A ⧸ (J ∩ fA)`-module**, by an
  isomorphism in the categorical pullback — so with the compatibility over the exceptional
  corner retained.

## Implementation notes

The two objects are moved to the common stage `n₁ + n₂` by
`CategoryTheory.EndoColim.objShiftIso`, on the modification after a
`CategoryTheory.EndoColim.stageCastIso` comparing `n₁ + n₂` with `n₂ + n₁`; this is the device of
`CategoryTheory.EndoColim.bijective_desc_map`. The structural isomorphism is presented at a
finite level by `CategoryTheory.EndoColim.exists_iso_hom_eq`, and the resulting isomorphism
between Frobenius iterates of the two restrictions to the exceptional corner is conjugated into
an isomorphism between the restrictions of the Frobenius iterates by
`CategoryTheory.EndoColim.squareIter`. The conclusion is stated in the conjugated form rather
than as an equality of isomorphisms, so that the honest isomorphism `u` of vector bundles — the
input to Milnor patching — appears on its own.

The data of the exceptional corner is given names here rather than reused: the names
`AlgebraicGeometry.OneGeneratorSquare.vectCtr` and friends of
`StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectFull` cover only
the two legs out of `Spec A`.

The essential surjectivity itself is *not* proved here. The compatibility displayed by
`AlgebraicGeometry.exists_presented_compatible_pair` is already in the shape the constructor
`CategoryTheory.Limits.CategoricalPullback.mkIso` consumes, so what the last step needs is an
object of `colim_F Vect(Spec A)` whose image under the comparison functor is the compatible pair
`(ℰ₁, ℰ₂, u)` placed at a stage; the candidate is
`AlgebraicGeometry.OneGeneratorSquare.betaGluedVect` of the module produced by
`AlgebraicGeometry.exists_finProj_of_vect_pair`. Three identifications are missing for that:

* the comparison `AlgebraicGeometry.squareColimVectIso` at an object, which computes the
  structural isomorphism of `AlgebraicGeometry.colimVectComparison` at `(ℰ, n)` as the stage-`n`
  functor applied to `AlgebraicGeometry.OneGeneratorSquare.squareVectIso` at `ℰ`;
* the image under `CategoryTheory.EndoColim.map` of the stage shift
  `CategoryTheory.EndoColim.objShiftIso`, without which the `N`-th Frobenius twists of
  `AlgebraicGeometry.OneGeneratorSquare.betaGluedVectCentreTwistIso` and
  `…betaGluedVectModificationTwistIso` cannot be absorbed into the stage *compatibly* on the two
  legs of the square;
* the agreement of the structural isomorphism of
  `MilnorPatching.OneGeneratorFrobenius.finProjComparison`, which is the canonical comparison of
  the two iterated extensions of scalars, with
  `AlgebraicGeometry.OneGeneratorSquare.squareVectIso`, which is the canonical comparison of the
  two iterated restrictions. This is the compatibility of
  `AlgebraicGeometry.tildeVectPullbackIso` with composition of ring maps, and
  `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` is constructed by uniqueness of
  left adjoints, so no such coherence is available for it in this repository.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe v u

/-! ### An isomorphism of the colimit category, presented after conjugation -/

namespace CategoryTheory.EndoColim

/-- **An isomorphism of `colim_F C` between two objects placed at one and the same stage is
presented at a finite level by an isomorphism of `C`, read through prescribed identifications of
the Frobenius iterates of its source and its target.** Given families of isomorphisms
`a j : F^j E ≅ X j` and `b j : F^j G ≅ Y j`, an isomorphism `(E, m) ≅ (G, m)` of `colim_F C` is
presented at some level `k` by an isomorphism `X (m + k) ≅ Y (m + k)`, conjugated by `a` and `b`.

This is `CategoryTheory.EndoColim.exists_iso_hom_eq` with the presenting isomorphism moved
across the two identifications, which is how the comparison
`CategoryTheory.EndoColim.squareIter` is absorbed: for a functor induced on the colimit
categories the iterate `F'^j (Φ E)` is identified with `Φ (F^j E)`, and it is the latter which
the gluing problem downstream is stated for. -/
theorem exists_conj_iso_hom_eq {C : Type u} [Category.{v} C] {F : C ⥤ C} {m : ℕ} {E G : C}
    (X Y : ℕ → C) (a : ∀ j : ℕ, (F.endoIter j).obj E ≅ X j)
    (b : ∀ j : ℕ, (F.endoIter j).obj G ≅ Y j) (e : (⟨E, m⟩ : EndoColim F) ≅ ⟨G, m⟩) :
    ∃ (k : ℕ) (u : X (m + k) ≅ Y (m + k)),
      e.hom = Hom.of k ((a (m + k)).hom ≫ u.hom ≫ (b (m + k)).inv) := by
  obtain ⟨k, u₀, hu₀⟩ := exists_iso_hom_eq e
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : (F.endoIter (m + k)).obj E ≅ (F.endoIter (m + k)).obj G,
      Hom.of k u₁.hom = e.hom := ⟨u₀, hu₀⟩
  refine ⟨k, (a (m + k)).symm ≪≫ u₁ ≪≫ b (m + k), ?_⟩
  refine Eq.trans hu₁.symm (congrArg (@Hom.of _ _ _ _ _ k) ?_)
  simp

end CategoryTheory.EndoColim

/-! ### Categorical pullbacks along a transformation of cospans -/

namespace CategoryTheory.Limits.CategoricalPullback

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] {F : A ⥤ B} {G : C ⥤ B}
  {A' B' C' : Type*} [Category* A'] [Category* B'] [Category* C'] {F' : A' ⥤ B'} {G' : C' ⥤ B'}

/-- **The functor between categorical pullbacks induced by a transformation of cospans.** A
transformation `ψ` of the cospan `F, G` into the cospan `F', G'` carries a compatible pair
`(a, c, F a ≅ G c)` to the pair `(ψ.left a, ψ.right c)`, the isomorphism of their images being
the given one transported by `ψ.base` and conjugated by the two 2-commutativity isomorphisms
of `ψ`. -/
def mapCospan (ψ : CatCospanTransform F G F' G') :
    CategoricalPullback F G ⥤ CategoricalPullback F' G' where
  obj x :=
    { fst := ψ.left.obj x.fst
      snd := ψ.right.obj x.snd
      iso := (ψ.squareLeft.iso.app x.fst).symm ≪≫ ψ.base.mapIso x.iso ≪≫
        ψ.squareRight.iso.app x.snd }
  map {x y} φ :=
    { fst := ψ.left.map φ.fst
      snd := ψ.right.map φ.snd
      w := by
        have hL := ψ.squareLeft.iso.inv.naturality φ.fst
        have hR := ψ.squareRight.iso.hom.naturality φ.snd
        simp only [Functor.comp_map] at hL hR
        simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
          Category.assoc]
        rw [reassoc_of% hL, ← Functor.map_comp_assoc, φ.w, Functor.map_comp_assoc, hR] }
  map_id x := by ext <;> simp
  map_comp φ χ := by ext <;> simp

/-- The first component of the induced functor is `ψ.left`. -/
@[simp]
lemma mapCospan_obj_fst (ψ : CatCospanTransform F G F' G') (x : CategoricalPullback F G) :
    ((mapCospan ψ).obj x).fst = ψ.left.obj x.fst :=
  rfl

/-- The second component of the induced functor is `ψ.right`. -/
@[simp]
lemma mapCospan_obj_snd (ψ : CatCospanTransform F G F' G') (x : CategoricalPullback F G) :
    ((mapCospan ψ).obj x).snd = ψ.right.obj x.snd :=
  rfl

/-- The structural isomorphism carried by the image of a compatible pair under the induced
functor. -/
@[simp]
lemma mapCospan_obj_iso_hom (ψ : CatCospanTransform F G F' G') (x : CategoricalPullback F G) :
    ((mapCospan ψ).obj x).iso.hom =
      (ψ.squareLeft.iso.app x.fst).inv ≫ ψ.base.map x.iso.hom ≫
        (ψ.squareRight.iso.app x.snd).hom :=
  rfl

/-- **The functor between categorical pullbacks induced by a transformation of cospans is
essentially surjective** as soon as the two outer functors of the transformation are and the
middle one is fully faithful. The two components of a compatible pair downstairs are lifted by
essential surjectivity, and the structural isomorphism is lifted by full faithfulness after
being conjugated into an isomorphism between the images under `ψ.base`; the conjugation is
exactly what makes the lifted pair map to a pair isomorphic to the given one. -/
theorem essSurj_mapCospan (ψ : CatCospanTransform F G F' G') (hl : ψ.left.EssSurj)
    (hr : ψ.right.EssSurj) (hfull : ψ.base.Full) (hfaithful : ψ.base.Faithful) :
    (mapCospan ψ).EssSurj where
  mem_essImage y := by
    have := hl
    have := hr
    have := hfull
    have := hfaithful
    refine ⟨{ fst := ψ.left.objPreimage y.fst
              snd := ψ.right.objPreimage y.snd
              iso := ψ.base.preimageIso (ψ.squareLeft.iso.app (ψ.left.objPreimage y.fst) ≪≫
                F'.mapIso (ψ.left.objObjPreimageIso y.fst) ≪≫ y.iso ≪≫
                  (G'.mapIso (ψ.right.objObjPreimageIso y.snd)).symm ≪≫
                    (ψ.squareRight.iso.app (ψ.right.objPreimage y.snd)).symm) }, ⟨?_⟩⟩
    refine mkIso (by exact ψ.left.objObjPreimageIso y.fst)
      (by exact ψ.right.objObjPreimageIso y.snd) ?_
    simp

end CategoryTheory.Limits.CategoricalPullback

namespace AlgebraicGeometry

namespace OneGeneratorSquare

/-! ### The data of the exceptional corner -/

section Corner

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime]
  (hp : (p : A) = 0)

/-- **The iterated Frobenius comparison on the leg from the centre into the exceptional
corner**: the `k`-fold Frobenius pullback on the corner of the restriction of `ℰ` is the
restriction of the `k`-fold Frobenius pullback of `ℰ`. -/
abbrev ctrCornerSquareIter (k : ℕ) (E : (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect) :
    ((frobExc A f J p hp).endoIter k).obj ((vectCtrExc A f J).obj E) ≅
      (vectCtrExc A f J).obj (((frobCtr A f p hp).endoIter k).obj E) :=
  EndoColim.squareIter (frobCtr A f p hp) (frobExc A f J p hp) (vectCtrExc A f J)
    (frobVectIsoCtrExc A f J p hp) k E

/-- **The iterated Frobenius comparison on the leg from the modification into the exceptional
corner**: the `k`-fold Frobenius pullback on the corner of the restriction of `ℰ` is the
restriction of the `k`-fold Frobenius pullback of `ℰ`. -/
abbrev modCornerSquareIter (k : ℕ) (E : (Spec (CommRingCat.of (A ⧸ J))).Vect) :
    ((frobExc A f J p hp).endoIter k).obj ((vectModExc A f J).obj E) ≅
      (vectModExc A f J).obj (((frobMod A J p hp).endoIter k).obj E) :=
  EndoColim.squareIter (frobMod A J p hp) (frobExc A f J p hp) (vectModExc A f J)
    (frobVectIsoModExc A f J p hp) k E

end Corner

/-! ### Moving the two components of an object to a common stage -/

section CommonStage

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime]
  (hp : (p : A) = 0)
  (Y : CategoricalPullback (centreToExceptional A f J p hp)
    (modificationToExceptional A f J p hp))

/-- **The centre component of an object of the categorical pullback, moved to the common
stage.** If `Y.fst = (ℰ₁, n₁)` and `Y.snd = (ℰ₂, n₂)`, this is the isomorphism
`(F_Z^{n₂,*}ℰ₁, n₁ + n₂) ≅ (ℰ₁, n₁)` of Stacks Tag 0EXA. -/
def commonStageCentreIso :
    (⟨((frobCtr A f p hp).endoIter Y.snd.stage).obj Y.fst.obj,
        Y.fst.stage + Y.snd.stage⟩ : colimVectCentre A f p hp) ≅ Y.fst :=
  EndoColim.objShiftIso (frobCtr A f p hp) Y.fst.stage Y.snd.stage Y.fst.obj

/-- **The modification component of an object of the categorical pullback, moved to the common
stage.** If `Y.fst = (ℰ₁, n₁)` and `Y.snd = (ℰ₂, n₂)`, this is the isomorphism
`(F_{X'}^{n₁,*}ℰ₂, n₁ + n₂) ≅ (ℰ₂, n₂)` of Stacks Tag 0EXA, after the comparison of the stage
`n₁ + n₂` with the stage `n₂ + n₁` at which that isomorphism is stated. -/
def commonStageModificationIso :
    (⟨((frobMod A J p hp).endoIter Y.fst.stage).obj Y.snd.obj,
        Y.fst.stage + Y.snd.stage⟩ : colimVectModification A J p hp) ≅ Y.snd :=
  EndoColim.stageCastIso (frobMod A J p hp)
      (((frobMod A J p hp).endoIter Y.fst.stage).obj Y.snd.obj)
      (Nat.add_comm Y.fst.stage Y.snd.stage) ≪≫
    EndoColim.objShiftIso (frobMod A J p hp) Y.snd.stage Y.fst.stage Y.snd.obj

end CommonStage

end OneGeneratorSquare

/-! ### An object of the categorical pullback, presented at a finite level -/

/-- **An object of the categorical pullback of Stacks Tag 0EXC is isomorphic to a compatible
pair presented at a finite level.** Given an object `Y` — a pair of objects of the colimit
categories of the centre and the modification together with an isomorphism of their images in
the colimit category of the exceptional corner — there are a common stage `m`, vector bundles
`ℰ₁` on the centre and `ℰ₂` on the modification placed at that stage and isomorphic to the two
components of `Y`, a level `k`, and an **isomorphism `u` of vector bundles on the exceptional
corner** between the restrictions of the `m + k`-th Frobenius twists of `ℰ₁` and of `ℰ₂`, which
presents the structural isomorphism of `Y` transported along those two isomorphisms.

This is the reduction of the essential surjectivity of the comparison functor to the
object-level gluing problem: the triple `(ℰ₁, ℰ₂, u)` is exactly the input of
`AlgebraicGeometry.exists_vect_of_compatible_pair`, after the Frobenius twists are absorbed into
the stage. -/
theorem exists_presented_compatible_pair (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (Y : CategoricalPullback (OneGeneratorSquare.centreToExceptional A f J p hp)
      (OneGeneratorSquare.modificationToExceptional A f J p hp)) :
    ∃ (m k : ℕ) (E₁ : (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect)
      (E₂ : (Spec (CommRingCat.of (A ⧸ J))).Vect)
      (σ₁ : (⟨E₁, m⟩ : OneGeneratorSquare.colimVectCentre A f p hp) ≅ Y.fst)
      (σ₂ : (⟨E₂, m⟩ : OneGeneratorSquare.colimVectModification A J p hp) ≅ Y.snd)
      (u : (OneGeneratorSquare.vectCtrExc A f J).obj
            (((OneGeneratorSquare.frobCtr A f p hp).endoIter (m + k)).obj E₁) ≅
          (OneGeneratorSquare.vectModExc A f J).obj
            (((OneGeneratorSquare.frobMod A J p hp).endoIter (m + k)).obj E₂)),
      (OneGeneratorSquare.centreToExceptional A f J p hp).map σ₁.hom ≫ Y.iso.hom ≫
          (OneGeneratorSquare.modificationToExceptional A f J p hp).map σ₂.inv =
        EndoColim.Hom.of k
          ((OneGeneratorSquare.ctrCornerSquareIter A f J p hp (m + k) E₁).hom ≫ u.hom ≫
            (OneGeneratorSquare.modCornerSquareIter A f J p hp (m + k) E₂).inv) := by
  obtain ⟨k, u, hu⟩ := EndoColim.exists_conj_iso_hom_eq
    (fun j ↦ (OneGeneratorSquare.vectCtrExc A f J).obj
      (((OneGeneratorSquare.frobCtr A f p hp).endoIter j).obj
        (((OneGeneratorSquare.frobCtr A f p hp).endoIter Y.snd.stage).obj Y.fst.obj)))
    (fun j ↦ (OneGeneratorSquare.vectModExc A f J).obj
      (((OneGeneratorSquare.frobMod A J p hp).endoIter j).obj
        (((OneGeneratorSquare.frobMod A J p hp).endoIter Y.fst.stage).obj Y.snd.obj)))
    (fun j ↦ OneGeneratorSquare.ctrCornerSquareIter A f J p hp j
      (((OneGeneratorSquare.frobCtr A f p hp).endoIter Y.snd.stage).obj Y.fst.obj))
    (fun j ↦ OneGeneratorSquare.modCornerSquareIter A f J p hp j
      (((OneGeneratorSquare.frobMod A J p hp).endoIter Y.fst.stage).obj Y.snd.obj))
    ((OneGeneratorSquare.centreToExceptional A f J p hp).mapIso
          (OneGeneratorSquare.commonStageCentreIso A f J p hp Y) ≪≫ Y.iso ≪≫
      ((OneGeneratorSquare.modificationToExceptional A f J p hp).mapIso
        (OneGeneratorSquare.commonStageModificationIso A f J p hp Y)).symm)
  refine ⟨Y.fst.stage + Y.snd.stage, k,
    ((OneGeneratorSquare.frobCtr A f p hp).endoIter Y.snd.stage).obj Y.fst.obj,
    ((OneGeneratorSquare.frobMod A J p hp).endoIter Y.fst.stage).obj Y.snd.obj,
    OneGeneratorSquare.commonStageCentreIso A f J p hp Y,
    OneGeneratorSquare.commonStageModificationIso A f J p hp Y, u, ?_⟩
  exact Eq.trans rfl hu

/-! ### A compatible pair of vector bundles comes from a finite projective module -/

/-- **The affine comparison as a transformation of the cospans of the square of Example
0EVG.** On each of the two corners `A ⧸ J` and `A ⧸ fA` and on the exceptional corner
`A ⧸ (J + fA)` it is the comparison `AlgebraicGeometry.tildeVect` of finite projective modules
with vector bundles, and the two 2-commutativity isomorphisms are the base-change compatibility
`AlgebraicGeometry.tildeVectPullbackIso` of that comparison along the two surjections onto the
exceptional corner. -/
def tildeCornerCospanTransform (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    CatCospanTransform
      (FinProj.extendScalars (CommRingCat.ofHom (MilnorPatching.OneGeneratorFrobenius.toBase f J)))
      (FinProj.extendScalars
        (CommRingCat.ofHom (MilnorPatching.OneGeneratorFrobenius.surjection f J)))
      (OneGeneratorSquare.vectModExc A f J) (OneGeneratorSquare.vectCtrExc A f J) where
  left := tildeVect (CommRingCat.of (A ⧸ J))
  base := tildeVect (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))
  right := tildeVect (CommRingCat.of (A ⧸ Ideal.span {f}))
  squareLeft :=
    { iso := (tildeVectPullbackIso
        (CommRingCat.ofHom (MilnorPatching.OneGeneratorFrobenius.toBase f J))).symm }
  squareRight :=
    { iso := (tildeVectPullbackIso
        (CommRingCat.ofHom (MilnorPatching.OneGeneratorFrobenius.surjection f J))).symm }

/-- **A compatible pair of vector bundles over the exceptional corner of the square of
Example 0EVG comes from a finite projective `A ⧸ (J ∩ fA)`-module.** A vector bundle on the
modification, a vector bundle on the centre and an isomorphism of their restrictions to the
exceptional corner — that is, an object of the categorical pullback of the two restriction
functors — is isomorphic, *in that categorical pullback*, to the image of a finite projective
`A ⧸ (J ∩ fA)`-module under the canonical comparison
`MilnorPatching.OneGeneratorFrobenius.finProjComparison` of Stacks Tag 0D2J, read on vector
bundles through the affine comparison.

This is the gluing step of Stacks Tag 0EXC with the compatibility over the exceptional corner
retained, which is what
`MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProj_obj` adds to the two separate
reduction isomorphisms of `AlgebraicGeometry.exists_vect_of_compatible_pair`. -/
theorem exists_finProj_of_vect_pair (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (W : CategoricalPullback (OneGeneratorSquare.vectModExc A f J)
      (OneGeneratorSquare.vectCtrExc A f J)) :
    ∃ L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))),
      Nonempty ((CategoricalPullback.mapCospan (tildeCornerCospanTransform A f J)).obj
        ((MilnorPatching.OneGeneratorFrobenius.finProjComparison A f J).obj L) ≅ W) := by
  have := CategoricalPullback.essSurj_mapCospan (tildeCornerCospanTransform A f J)
    (tildeVect_essSurj (CommRingCat.of (A ⧸ J)))
    (tildeVect_essSurj (CommRingCat.of (A ⧸ Ideal.span {f})))
    (tildeVect_full (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f}))))
    (tildeVect_faithful (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f}))))
  obtain ⟨L, ⟨eL⟩⟩ := MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProj_obj A f J
    ((CategoricalPullback.mapCospan (tildeCornerCospanTransform A f J)).objPreimage W)
  exact ⟨L, ⟨(CategoricalPullback.mapCospan (tildeCornerCospanTransform A f J)).mapIso eL ≪≫
    (CategoricalPullback.mapCospan (tildeCornerCospanTransform A f J)).objObjPreimageIso W⟩⟩

/-- The vector bundle on the modification attached to a finite projective
`A ⧸ (J ∩ fA)`-module by `AlgebraicGeometry.exists_finProj_of_vect_pair` is the one attached to
its reduction to `A ⧸ J`. -/
lemma mapCospan_finProjComparison_obj_fst (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) :
    ((CategoricalPullback.mapCospan (tildeCornerCospanTransform A f J)).obj
        ((MilnorPatching.OneGeneratorFrobenius.finProjComparison A f J).obj L)).fst =
      (tildeVect (CommRingCat.of (A ⧸ J))).obj
        ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).obj L) :=
  rfl

/-- The vector bundle on the centre attached to a finite projective `A ⧸ (J ∩ fA)`-module by
`AlgebraicGeometry.exists_finProj_of_vect_pair` is the one attached to its reduction to
`A ⧸ fA`. -/
lemma mapCospan_finProjComparison_obj_snd (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) :
    ((CategoricalPullback.mapCospan (tildeCornerCospanTransform A f J)).obj
        ((MilnorPatching.OneGeneratorFrobenius.finProjComparison A f J).obj L)).snd =
      (tildeVect (CommRingCat.of (A ⧸ Ideal.span {f}))).obj
        ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).obj L) :=
  rfl

namespace OneGeneratorSquare

/-! ### The vector bundle glued from a finite projective module -/

section Glued

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
  (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
  (N : ℕ) (hN : n + 1 ≤ p ^ N)
  (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))))

/-- **The vector bundle on `Spec A` glued from a finite projective `A ⧸ (J ∩ fA)`-module**: the
restriction of `L^~` along `Spec` of the Frobenius factorisation
`MilnorPatching.OneGeneratorFrobenius.betaHom`. -/
def betaGluedVect : (Spec (CommRingCat.of A)).Vect :=
  (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.betaHom hann p hp N hN)))).obj
    ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L)

/-- **The restriction to the centre of the vector bundle glued from `L`** is the `p ^ N`-power
restriction of the reduction of `L` to `A ⧸ fA`. The two restrictions are compared by
`AlgebraicGeometry.vectPullbackSquareIso` for the commuting square
`AlgebraicGeometry.OneGeneratorSquare.specMap_betaHom_centre_square`, and the reduction of `L` is
recognised by `AlgebraicGeometry.tildeVectPullbackIso`. -/
def betaGluedVectCentreIso :
    (Scheme.Vect.pullback (Spec.map (toCtr A f))).obj (betaGluedVect A f J n hann p hp N hN L) ≅
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ Ideal.span {f}) p
            (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N)))).obj
        ((tildeVect (CommRingCat.of (A ⧸ Ideal.span {f}))).obj
          ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
            (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).obj L)) :=
  (vectPullbackSquareIso (specMap_betaHom_centre_square A f J n hann p hp N hN)).app
      ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≪≫
    (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ Ideal.span {f}) p
        (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N)))).mapIso
      ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
        (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).app L)

/-- **The restriction to the modification of the vector bundle glued from `L`** is the
`p ^ N`-power restriction of the reduction of `L` to `A ⧸ J`. The two restrictions are compared
by `AlgebraicGeometry.vectPullbackSquareIso` for the commuting square
`AlgebraicGeometry.OneGeneratorSquare.specMap_betaHom_modification_square`, and the reduction of
`L` is recognised by `AlgebraicGeometry.tildeVectPullbackIso`. -/
def betaGluedVectModificationIso :
    (Scheme.Vect.pullback (Spec.map (toMod A J))).obj (betaGluedVect A f J n hann p hp N hN L) ≅
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ J) p
            (natCast_quotient_eq_zero A p hp J) N)))).obj
        ((tildeVect (CommRingCat.of (A ⧸ J))).obj
          ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
            (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).obj L)) :=
  (vectPullbackSquareIso (specMap_betaHom_modification_square A f J n hann p hp N hN)).app
      ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≪≫
    (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow (A ⧸ J) p
        (natCast_quotient_eq_zero A p hp J) N)))).mapIso
      ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
        (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).app L)

/-- **The restriction to the centre of the vector bundle glued from `L` is the `N`-th Frobenius
twist of the reduction of `L` to `A ⧸ fA`.** This is
`AlgebraicGeometry.OneGeneratorSquare.betaGluedVectCentreIso` with the restriction along the
`p ^ N`-power map recognised as the `N`-fold Frobenius pullback by
`AlgebraicGeometry.frobeniusPullbackIterSpecIso`; the twist is spelled as an iterate of
`AlgebraicGeometry.frobeniusPullback`, which is the endofunctor whose colimit category is
`colim_F Vect(Spec (A ⧸ fA))`. -/
def betaGluedVectCentreTwistIso :
    (Scheme.Vect.pullback (Spec.map (toCtr A f))).obj (betaGluedVect A f J n hann p hp N hN L) ≅
      ((frobCtr A f p hp).endoIter N).obj
        ((tildeVect (CommRingCat.of (A ⧸ Ideal.span {f}))).obj
          ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
            (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).obj L)) :=
  betaGluedVectCentreIso A f J n hann p hp N hN L ≪≫
    (frobeniusPullbackIterSpecIso (A ⧸ Ideal.span {f}) p
      (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N).symm.app _

/-- **The restriction to the modification of the vector bundle glued from `L` is the `N`-th
Frobenius twist of the reduction of `L` to `A ⧸ J`.** This is
`AlgebraicGeometry.OneGeneratorSquare.betaGluedVectModificationIso` with the restriction along
the `p ^ N`-power map recognised as the `N`-fold Frobenius pullback by
`AlgebraicGeometry.frobeniusPullbackIterSpecIso`. -/
def betaGluedVectModificationTwistIso :
    (Scheme.Vect.pullback (Spec.map (toMod A J))).obj (betaGluedVect A f J n hann p hp N hN L) ≅
      ((frobMod A J p hp).endoIter N).obj
        ((tildeVect (CommRingCat.of (A ⧸ J))).obj
          ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
            (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).obj L)) :=
  betaGluedVectModificationIso A f J n hann p hp N hN L ≪≫
    (frobeniusPullbackIterSpecIso (A ⧸ J) p (natCast_quotient_eq_zero A p hp J) N).symm.app _

end Glued

end OneGeneratorSquare

end AlgebraicGeometry

end
