module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMap
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPower
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVectQuotient
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVect
public import StacksFrontier.RingTheory.Module.BaseChangeQuotientHom

/-!
# Fullness of the comparison of Stacks Tag 0EXC

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be an
ideal, so that the spectra of

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

form the almost blowup square of More on Flatness, Example 0EVG. This file proves **the fullness
half of Stacks Tag 0EXC**: a morphism of `colim_F Vect` on the centre `Spec (A ⧸ fA)` and a
morphism of `colim_F Vect` on the modification `Spec (A ⧸ J)` which agree over the exceptional
corner `Spec (A ⧸ (J + fA))` come from a single morphism of `colim_F Vect(Spec A)`.

The input is the Milnor patching statement
`AlgebraicGeometry.exists_hom_of_pullback_pair`: a pair of morphisms of the restrictions of two
vector bundles on `Spec A` to `Spec (A ⧸ J)` and to `Spec (A ⧸ fA)` which is *realized* by a pair
of morphisms upstairs agreeing over `Spec (A ⧸ (J + fA))` is realized by a single morphism
upstairs. What that statement still needs is the realizability of each of the two morphisms
separately, which is the fullness of restriction along a closed immersion
`Spec (A ⧸ 𝔞) ⟶ Spec A` on vector bundles, proved here out of
`Stacks.BaseChangeQuotient.exists_baseChange_quotient_eq`.

On the colimit categories of Stacks Tag 0EXA a morphism is presented at a level, and by
`CategoryTheory.EndoColim.map_map_of` the morphisms which arise from upstairs are exactly the
`CategoryTheory.EndoColim.transportHom`s — the images under restriction of the presenting
morphisms, conjugated by the iterated Frobenius comparison
`CategoryTheory.EndoColim.squareIter`. So the hypothesis of the main theorem is phrased on the
*unconjugated* data, which is what `CategoryTheory.EndoColim.untransportHom` extracts from a
presentation, and `CategoryTheory.EndoColim.transportHom_eq_iff` is the dictionary between the
two.

## Main definitions

* `CategoryTheory.EndoColim.untransportHom`: the morphism between the images of iterates which a
  morphism between iterates at the images determines, by conjugating with
  `CategoryTheory.EndoColim.squareIter` the other way round.
* `AlgebraicGeometry.OneGeneratorSquare.excVectIso`: restricting a vector bundle on `Spec A` to
  the modification and then to the exceptional corner is restricting it along the quotient map
  `A ⟶ A ⧸ (J + fA)`.

## Main results

* `CategoryTheory.EndoColim.transportHom_eq_iff`: a morphism of `C` between iterates of `F`
  induces a prescribed morphism between the iterates of `F'` exactly when `Φ` carries it to the
  unconjugated form of that morphism.
* `CategoryTheory.EndoColim.Hom.exists_of_pair`: two morphisms, one in each of two colimit
  categories, are presented at a common level.
* `AlgebraicGeometry.exists_extendScalars_map_eq` and
  `AlgebraicGeometry.vect_pullback_quotient_full`: **the fullness input.** Extension of scalars
  along `A ⟶ A ⧸ 𝔞` is full on finite projective modules, hence restriction of vector bundles
  along `Spec (A ⧸ 𝔞) ⟶ Spec A` is a full functor.
* `AlgebraicGeometry.exists_colim_hom_of_presented_pair`: **the fullness half of Stacks Tag
  0EXC, at a common stage**, for a pair of morphisms presented at a common level.
* `AlgebraicGeometry.exists_colim_hom_of_pair`: the same for a pair of morphisms of the colimit
  categories which is not handed over in a presented form.

## Implementation notes

Restriction of vector bundles along `Spec (A ⧸ 𝔞) ⟶ Spec A` is shown to be full by transporting
the fullness of extension of scalars across the affine comparison
`AlgebraicGeometry.tildeVectPullbackIso`: that comparison exhibits the restriction functor as
naturally isomorphic to `(tildeVect A)⁻¹ ⋙ extendScalars ⋙ tildeVect (A ⧸ 𝔞)`, a composite of
full functors, so `CategoryTheory.Functor.Full.of_iso` applies. The three fullness instances are
supplied by hand with `haveI` rather than left to instance search, which does not find
`AlgebraicGeometry.tildeVect_full` at the concrete ring `CommRingCat.of (A ⧸ 𝔞)`.

The four functors and the two Frobenius comparisons of the square are given reducible names
(`AlgebraicGeometry.OneGeneratorSquare.vectCtr` and friends), without which the statements below
do not fit on a page; being `abbrev`s they are transparent to unification, which is what lets
`CategoryTheory.EndoColim.map_map_of` apply to
`AlgebraicGeometry.OneGeneratorSquare.toCentre` on the nose.

Every equation produced by the Milnor patching input is spelled with the literal quotient map
`CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)`, whereas the square uses the names
`AlgebraicGeometry.OneGeneratorSquare.toCtr` and
`AlgebraicGeometry.OneGeneratorSquare.toMod` for the same morphisms. The two spellings are
definitionally equal but not syntactically so, and `rw` sees only the syntax; the two `have`s
with an underscore on the right-hand side in the proof of
`AlgebraicGeometry.exists_colim_hom_of_presented_pair` restate the hypotheses in the spelling the
rewrites need.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe v u u₂

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C']

section Square

variable (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')

/-- **The morphism between the images under `Φ` of iterates of `F` which a morphism between
iterates of `F'` at the images determines**: the conjugate of `x` by the iterated comparison
`CategoryTheory.EndoColim.squareIter`, which runs the conjugation of
`CategoryTheory.EndoColim.transportHom` backwards. A morphism of `colim_{F'} C'` presented at a
level by `x` comes from `colim_F C` exactly when this morphism is in the image of `Φ`. -/
def untransportHom (a : ℕ) {E G : C}
    (x : (F'.endoIter a).obj (Φ.obj E) ⟶ (F'.endoIter a).obj (Φ.obj G)) :
    Φ.obj ((F.endoIter a).obj E) ⟶ Φ.obj ((F.endoIter a).obj G) :=
  (squareIter F F' Φ α a E).inv ≫ x ≫ (squareIter F F' Φ α a G).hom

/-- **A morphism of `C` between iterates of `F` induces a prescribed morphism between the
iterates of `F'` exactly when `Φ` carries it to the unconjugated form of that morphism.** Both
`CategoryTheory.EndoColim.transportHom` and
`CategoryTheory.EndoColim.untransportHom` are conjugations by the iterated comparison, in
opposite directions, so each undoes the other. -/
lemma transportHom_eq_iff (a : ℕ) {E G : C}
    (h : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G)
    (x : (F'.endoIter a).obj (Φ.obj E) ⟶ (F'.endoIter a).obj (Φ.obj G)) :
    transportHom F F' Φ α a h = x ↔ Φ.map h = untransportHom F F' Φ α a x := by
  rw [untransportHom, transportHom]
  constructor
  · rintro rfl
    simp
  · intro hx
    rw [hx]
    simp

/-- The induced functor sends the morphism presented at level `k` by `h` to the one presented by
`x`, once `Φ` carries `h` to the unconjugated form of `x`. -/
private lemma map_map_of_eq_of_map_eq (n k : ℕ) {E G : C}
    (h : (F.endoIter (n + k)).obj E ⟶ (F.endoIter (n + k)).obj G)
    (x : (F'.endoIter (n + k)).obj (Φ.obj E) ⟶ (F'.endoIter (n + k)).obj (Φ.obj G))
    (hx : Φ.map h = untransportHom F F' Φ α (n + k) x) :
    (map F F' Φ α).map (Hom.of k h : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩) =
      (Hom.of k x : (⟨Φ.obj E, n⟩ : EndoColim F') ⟶ ⟨Φ.obj G, n⟩) :=
  (map_map_of F F' Φ α n k h).trans
    (congrArg (Hom.of k) ((transportHom_eq_iff F F' Φ α (n + k) h x).mpr hx))

end Square

/-! ### Raising two presentations to a common level -/

/-- **A morphism of `colim_F C` presented at level `k` is presented at every larger level**,
and at every level equal to a sum `k + l`. -/
lemma Hom.exists_of_add {F : C ⥤ C} {A B : EndoColim F} {k : ℕ}
    (x : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj)
    {l N : ℕ} (h : k + l = N) :
    ∃ y : (F.endoIter (B.stage + N)).obj A.obj ⟶ (F.endoIter (A.stage + N)).obj B.obj,
      Hom.of N y = Hom.of k x := by
  subst h
  exact ⟨_, Hom.of_raise k x l⟩

/-- **A morphism of `colim_F C` and a morphism of `colim_{F'} C'` are presented at a common
level.** Each is raised to the level `k + l`, where `k` and `l` are the levels at which they are
presented. -/
lemma Hom.exists_of_pair {F : C ⥤ C} {F' : C' ⥤ C'} {A B : EndoColim F} {A' B' : EndoColim F'}
    (u : A ⟶ B) (v : A' ⟶ B') :
    ∃ (N : ℕ)
      (x : (F.endoIter (B.stage + N)).obj A.obj ⟶ (F.endoIter (A.stage + N)).obj B.obj)
      (y : (F'.endoIter (B'.stage + N)).obj A'.obj ⟶ (F'.endoIter (A'.stage + N)).obj B'.obj),
      Hom.of N x = u ∧ Hom.of N y = v := by
  obtain ⟨k, x, rfl⟩ := Hom.exists_of u
  obtain ⟨l, y, rfl⟩ := Hom.exists_of v
  obtain ⟨x', hx'⟩ := Hom.exists_of_add x rfl
  obtain ⟨y', hy'⟩ := Hom.exists_of_add y (show l + k = k + l by omega)
  exact ⟨k + l, x', y', hx', hy'⟩

end CategoryTheory.EndoColim

namespace AlgebraicGeometry

/-! ### Fullness of reduction modulo an ideal -/

/-- **Extension of scalars along the quotient map `A ⟶ A ⧸ 𝔞` is full on finite projective
modules.** Every `A ⧸ 𝔞`-linear map between the reductions of two finite projective `A`-modules
is the reduction of an `A`-linear map; this is
`Stacks.BaseChangeQuotient.exists_baseChange_quotient_eq` read through the identification of
`ModuleCat.extendScalars` with `LinearMap.baseChange`. -/
theorem exists_extendScalars_map_eq (A : Type u) [CommRing A] (𝔞 : Ideal A)
    {L L' : FinProj (CommRingCat.of A)}
    (ψ : (FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).obj L ⟶
      (FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).obj L') :
    ∃ χ : L ⟶ L',
      (FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).map χ = ψ := by
  let _ : Module.Finite A L.obj := L.property.1
  let _ : Module.Projective A L.obj := L.property.2
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : L.obj →ₗ[A] L'.obj, LinearMap.baseChange (A ⧸ 𝔞) h₀ = ψ.hom.hom :=
    Stacks.BaseChangeQuotient.exists_baseChange_quotient_eq 𝔞 _
  exact ⟨ObjectProperty.homMk (ModuleCat.ofHom h₀),
    ObjectProperty.hom_ext _ (ModuleCat.hom_ext hh₀)⟩

/-- **Restriction of vector bundles along the closed immersion `Spec (A ⧸ 𝔞) ⟶ Spec A` is
full.** The affine comparison `AlgebraicGeometry.tildeVectPullbackIso` identifies the restriction
functor with the composite of the inverse of the comparison on `Spec A`, extension of scalars,
and the comparison on `Spec (A ⧸ 𝔞)`; all three are full, the middle one by
`AlgebraicGeometry.exists_extendScalars_map_eq`. -/
theorem vect_pullback_quotient_full (A : Type u) [CommRing A] (𝔞 : Ideal A) :
    (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))).Full := by
  have : (FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).Full :=
    { map_surjective := exists_extendScalars_map_eq A 𝔞 }
  have : (tildeVect (CommRingCat.of (A ⧸ 𝔞))).Full := tildeVect_full _
  have : (tildeVectEquivalence (CommRingCat.of A)).inverse.Full := Equivalence.full_inverse _
  exact Functor.Full.of_iso
    (Functor.isoWhiskerLeft (tildeVectEquivalence (CommRingCat.of A)).inverse
        (tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).symm ≪≫
      (tildeVectEquivalence (CommRingCat.of A)).invFunIdAssoc _)

/-- **A morphism between the restrictions to `Spec (A ⧸ 𝔞)` of two vector bundles on `Spec A`
comes from a morphism of the bundles themselves.** This is
`AlgebraicGeometry.vect_pullback_quotient_full` read as an existence statement. -/
theorem exists_hom_of_pullback_quotient (A : Type u) [CommRing A] (𝔞 : Ideal A)
    {M₀ N₀ : (Spec (CommRingCat.of A)).Vect}
    (a : (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))).obj M₀ ⟶
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))).obj N₀) :
    ∃ h : M₀ ⟶ N₀,
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))).map h = a :=
  (vect_pullback_quotient_full A 𝔞).map_surjective a

/-! ### The data of the one-generator square -/

namespace OneGeneratorSquare

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime]
  (hp : (p : A) = 0)

/-- Restriction of vector bundles along the closed immersion of the centre,
`Spec (A ⧸ fA) ⟶ Spec A`. -/
abbrev vectCtr : (Spec (CommRingCat.of A)).Vect ⥤
    (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect :=
  Scheme.Vect.pullback (Spec.map (toCtr A f))

/-- Restriction of vector bundles along the closed immersion of the modification,
`Spec (A ⧸ J) ⟶ Spec A`. -/
abbrev vectMod : (Spec (CommRingCat.of A)).Vect ⥤ (Spec (CommRingCat.of (A ⧸ J))).Vect :=
  Scheme.Vect.pullback (Spec.map (toMod A J))

/-- Frobenius pullback of vector bundles on the base `Spec A` of the square, the endofunctor
whose colimit category is `colim_F Vect(Spec A)`. -/
abbrev frobBase : (Spec (CommRingCat.of A)).Vect ⥤ (Spec (CommRingCat.of A)).Vect :=
  frobeniusPullback (Spec (CommRingCat.of A)) p (charBase A p hp)

/-- Frobenius pullback of vector bundles on the centre `Spec (A ⧸ fA)` of the square. -/
abbrev frobCtr : (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect ⥤
    (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect :=
  frobeniusPullback (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))) p (charCtr A f p hp)

/-- Frobenius pullback of vector bundles on the modification `Spec (A ⧸ J)` of the square. -/
abbrev frobMod : (Spec (CommRingCat.of (A ⧸ J))).Vect ⥤ (Spec (CommRingCat.of (A ⧸ J))).Vect :=
  frobeniusPullback (Spec (CommRingCat.of (A ⧸ J))) p (charMod A J p hp)

/-- The comparison of `AlgebraicGeometry.frobeniusVectPullbackIso` for restriction to the
centre: Frobenius pullback commutes with restriction along `Spec (A ⧸ fA) ⟶ Spec A`. -/
abbrev frobVectIsoCtr : frobBase A p hp ⋙ vectCtr A f ≅ vectCtr A f ⋙ frobCtr A f p hp :=
  frobeniusVectPullbackIso (Spec.map (toCtr A f)) p (charCtr A f p hp) (charBase A p hp)

/-- The comparison of `AlgebraicGeometry.frobeniusVectPullbackIso` for restriction to the
modification: Frobenius pullback commutes with restriction along `Spec (A ⧸ J) ⟶ Spec A`. -/
abbrev frobVectIsoMod : frobBase A p hp ⋙ vectMod A J ≅ vectMod A J ⋙ frobMod A J p hp :=
  frobeniusVectPullbackIso (Spec.map (toMod A J)) p (charMod A J p hp) (charBase A p hp)

/-- **The composite `A ⟶ A ⧸ J ⟶ A ⧸ (J + fA)` of the square is the quotient map**, because
`MilnorPatching.OneGeneratorFrobenius.toBase` is the identity on representatives. Together with
`AlgebraicGeometry.OneGeneratorSquare.toMod_comp_modToExc` this identifies both composites of the
square with the quotient map. -/
theorem toMod_comp_modToExc_eq :
    toMod A J ≫ modToExc A f J =
      CommRingCat.ofHom (Ideal.Quotient.mk (J ⊔ Ideal.span {f})) := by
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  show MilnorPatching.OneGeneratorFrobenius.toBase f J (Ideal.Quotient.mk J x) =
    Ideal.Quotient.mk (J ⊔ Ideal.span {f}) x
  rw [MilnorPatching.OneGeneratorFrobenius.toBase_mk]

/-- **Restricting a vector bundle on `Spec A` to the modification and then to the exceptional
corner is restricting it along the quotient map `A ⟶ A ⧸ (J + fA)`**, by the
pseudofunctoriality of restriction and
`AlgebraicGeometry.OneGeneratorSquare.toMod_comp_modToExc_eq`. This is what carries the
compatibility over the exceptional corner into the form the Milnor patching input asks for. -/
def excVectIso :
    vectMod A J ⋙ Scheme.Vect.pullback (Spec.map (modToExc A f J)) ≅
      Scheme.Vect.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ⊔ Ideal.span {f})))) :=
  Scheme.Vect.pullbackComp (Spec.map (modToExc A f J)) (Spec.map (toMod A J)) ≪≫
    Scheme.Vect.pullbackCongr (by rw [← Spec.map_comp, toMod_comp_modToExc_eq])

end OneGeneratorSquare

/-! ### Fullness at a common stage -/

/-- **The fullness half of Stacks Tag 0EXC, at a common stage.** A morphism on the centre and a
morphism on the modification, presented at a common level `k` over the stage `m` by `a₀` and
`b₀`, and agreeing over the exceptional corner after transport by
`AlgebraicGeometry.OneGeneratorSquare.squareVectIso`, come from a morphism of
`colim_F Vect(Spec A)` which they present. The hypothesis is phrased on the unconjugated forms
`CategoryTheory.EndoColim.untransportHom` of `a₀` and `b₀`, which are the morphisms of vector
bundles on the centre and the modification that `a₀` and `b₀` amount to; by
`CategoryTheory.EndoColim.map_map_of` those are exactly the data a morphism from upstairs
produces. -/
theorem exists_colim_hom_of_presented_pair
    (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    {E G : (Spec (CommRingCat.of A)).Vect} (m k : ℕ)
    (a₀ : ((OneGeneratorSquare.frobCtr A f p hp).endoIter (m + k)).obj
        ((OneGeneratorSquare.vectCtr A f).obj E) ⟶
      ((OneGeneratorSquare.frobCtr A f p hp).endoIter (m + k)).obj
        ((OneGeneratorSquare.vectCtr A f).obj G))
    (b₀ : ((OneGeneratorSquare.frobMod A J p hp).endoIter (m + k)).obj
        ((OneGeneratorSquare.vectMod A J).obj E) ⟶
      ((OneGeneratorSquare.frobMod A J p hp).endoIter (m + k)).obj
        ((OneGeneratorSquare.vectMod A J).obj G))
    (hcompat :
      (OneGeneratorSquare.squareVectIso A f J).hom.app
            (((OneGeneratorSquare.frobBase A p hp).endoIter (m + k)).obj E) ≫
          (Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.ctrToExc A f J))).map
            (EndoColim.untransportHom (OneGeneratorSquare.frobBase A p hp)
              (OneGeneratorSquare.frobCtr A f p hp) (OneGeneratorSquare.vectCtr A f)
              (OneGeneratorSquare.frobVectIsoCtr A f p hp) (m + k) a₀) ≫
        (OneGeneratorSquare.squareVectIso A f J).inv.app
          (((OneGeneratorSquare.frobBase A p hp).endoIter (m + k)).obj G) =
      (Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.modToExc A f J))).map
        (EndoColim.untransportHom (OneGeneratorSquare.frobBase A p hp)
          (OneGeneratorSquare.frobMod A J p hp) (OneGeneratorSquare.vectMod A J)
          (OneGeneratorSquare.frobVectIsoMod A J p hp) (m + k) b₀)) :
    ∃ u : (⟨E, m⟩ : OneGeneratorSquare.colimVectBase A p hp) ⟶ ⟨G, m⟩,
      (OneGeneratorSquare.toCentre A f p hp).map u = EndoColim.Hom.of k a₀ ∧
      (OneGeneratorSquare.toModification A J p hp).map u = EndoColim.Hom.of k b₀ := by
  obtain ⟨h₂, hh₂⟩ := exists_hom_of_pullback_quotient A (Ideal.span {f})
    (EndoColim.untransportHom (OneGeneratorSquare.frobBase A p hp)
      (OneGeneratorSquare.frobCtr A f p hp) (OneGeneratorSquare.vectCtr A f)
      (OneGeneratorSquare.frobVectIsoCtr A f p hp) (m + k) a₀)
  obtain ⟨h₁, hh₁⟩ := exists_hom_of_pullback_quotient A J
    (EndoColim.untransportHom (OneGeneratorSquare.frobBase A p hp)
      (OneGeneratorSquare.frobMod A J p hp) (OneGeneratorSquare.vectMod A J)
      (OneGeneratorSquare.frobVectIsoMod A J p hp) (m + k) b₀)
  have hc₂ : (OneGeneratorSquare.vectCtr A f).map h₂ = _ := hh₂
  have hc₁ : (OneGeneratorSquare.vectMod A J).map h₁ = _ := hh₁
  have key := (NatIso.hom_app_comp_map_comp_inv_app
    (OneGeneratorSquare.squareVectIso A f J) h₂).symm
  simp only [Functor.comp_map] at key
  rw [hc₂, hcompat, ← hc₁] at key
  have hexc := (NatIso.map_eq_map_iff (OneGeneratorSquare.excVectIso A f J) h₂ h₁).mp key
  obtain ⟨h, hJ, hf⟩ := exists_hom_of_pullback_pair A f J _ _ h₁ h₂ hh₁ hh₂ hexc.symm
  refine ⟨EndoColim.Hom.of k h, ?_, ?_⟩
  · exact EndoColim.map_map_of_eq_of_map_eq _ _ _ _ m k h a₀ hf
  · exact EndoColim.map_map_of_eq_of_map_eq _ _ _ _ m k h b₀ hJ

/-! ### Fullness for arbitrary pairs of morphisms -/

/-- **Two morphisms of the colimit categories on the centre and on the modification are
presented at a common level**, so that the hypothesis of
`AlgebraicGeometry.exists_colim_hom_of_presented_pair` can be checked for them. -/
theorem exists_common_presentation_of_pair
    (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    {E G : (Spec (CommRingCat.of A)).Vect} (m : ℕ)
    (a : (OneGeneratorSquare.toCentre A f p hp).obj ⟨E, m⟩ ⟶
      (OneGeneratorSquare.toCentre A f p hp).obj ⟨G, m⟩)
    (b : (OneGeneratorSquare.toModification A J p hp).obj ⟨E, m⟩ ⟶
      (OneGeneratorSquare.toModification A J p hp).obj ⟨G, m⟩) :
    ∃ (k : ℕ)
      (a₀ : ((OneGeneratorSquare.frobCtr A f p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectCtr A f).obj E) ⟶
        ((OneGeneratorSquare.frobCtr A f p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectCtr A f).obj G))
      (b₀ : ((OneGeneratorSquare.frobMod A J p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectMod A J).obj E) ⟶
        ((OneGeneratorSquare.frobMod A J p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectMod A J).obj G)),
      EndoColim.Hom.of k a₀ = a ∧ EndoColim.Hom.of k b₀ = b :=
  EndoColim.Hom.exists_of_pair a b

/-- **The fullness half of Stacks Tag 0EXC**, for a pair of morphisms `a`, `b` of the colimit
categories which is not handed over in a presented form: if some common presentation of `a` and
`b` — one exists by `AlgebraicGeometry.exists_common_presentation_of_pair` — agrees over the
exceptional corner, then `a` and `b` are the images of a single morphism of
`colim_F Vect(Spec A)`. -/
theorem exists_colim_hom_of_pair
    (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    {E G : (Spec (CommRingCat.of A)).Vect} (m : ℕ)
    (a : (OneGeneratorSquare.toCentre A f p hp).obj ⟨E, m⟩ ⟶
      (OneGeneratorSquare.toCentre A f p hp).obj ⟨G, m⟩)
    (b : (OneGeneratorSquare.toModification A J p hp).obj ⟨E, m⟩ ⟶
      (OneGeneratorSquare.toModification A J p hp).obj ⟨G, m⟩)
    (hcompat : ∃ (k : ℕ)
      (a₀ : ((OneGeneratorSquare.frobCtr A f p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectCtr A f).obj E) ⟶
        ((OneGeneratorSquare.frobCtr A f p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectCtr A f).obj G))
      (b₀ : ((OneGeneratorSquare.frobMod A J p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectMod A J).obj E) ⟶
        ((OneGeneratorSquare.frobMod A J p hp).endoIter (m + k)).obj
          ((OneGeneratorSquare.vectMod A J).obj G)),
      EndoColim.Hom.of k a₀ = a ∧ EndoColim.Hom.of k b₀ = b ∧
        (OneGeneratorSquare.squareVectIso A f J).hom.app
              (((OneGeneratorSquare.frobBase A p hp).endoIter (m + k)).obj E) ≫
            (Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.ctrToExc A f J))).map
              (EndoColim.untransportHom (OneGeneratorSquare.frobBase A p hp)
                (OneGeneratorSquare.frobCtr A f p hp) (OneGeneratorSquare.vectCtr A f)
                (OneGeneratorSquare.frobVectIsoCtr A f p hp) (m + k) a₀) ≫
          (OneGeneratorSquare.squareVectIso A f J).inv.app
            (((OneGeneratorSquare.frobBase A p hp).endoIter (m + k)).obj G) =
        (Scheme.Vect.pullback (Spec.map (OneGeneratorSquare.modToExc A f J))).map
          (EndoColim.untransportHom (OneGeneratorSquare.frobBase A p hp)
            (OneGeneratorSquare.frobMod A J p hp) (OneGeneratorSquare.vectMod A J)
            (OneGeneratorSquare.frobVectIsoMod A J p hp) (m + k) b₀)) :
    ∃ u : (⟨E, m⟩ : OneGeneratorSquare.colimVectBase A p hp) ⟶ ⟨G, m⟩,
      (OneGeneratorSquare.toCentre A f p hp).map u = a ∧
      (OneGeneratorSquare.toModification A J p hp).map u = b := by
  obtain ⟨k, a₀, b₀, ha, hb, hc⟩ := hcompat
  obtain ⟨u, hu₁, hu₂⟩ := exists_colim_hom_of_presented_pair A f J p hp m k a₀ b₀ hc
  exact ⟨u, hu₁.trans ha, hu₂.trans hb⟩

end AlgebraicGeometry

end
