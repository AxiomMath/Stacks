module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Degrees multiply along a finite dominant morphism of proper varieties

Let `k` be a field and let `f : Y ⟶ X` be a finite dominant morphism of proper varieties over
`k`.  Let `𝓛` be an invertible `𝒪_X`-module.  [Stacks, Tag 0BEX] computes the degree of `Y` with
respect to the pullback as the degree of `f` times the degree of `X`:

`deg_{f^*𝓛}(Y) = deg(f) deg_𝓛(X)`,

the degree of `f` being `AlgebraicGeometry.degreeOver` of [Stacks, Morphisms, Definition 02NY]
and the degree of a variety being the self-intersection number `(𝓛^d · Z)` for `d` its
dimension, which is [Stacks, Tag 0BEW].

## Main results

* `AlgebraicGeometry.degreeWithRespectTo_pullback_of_isFinite`: **[Stacks, Tag 0BEX]**, the
  source's statement, for an ample invertible module and with both sides read as the degrees
  `deg_{f^*𝓛}(Y)` and `deg_𝓛(X)` of [Stacks, Tag 0BEW].
* `AlgebraicGeometry.selfIntersectionNumber_pullback_of_isFinite`: the same formula for an
  arbitrary invertible module, which is where the content is.
* `AlgebraicGeometry.isAmple_pullback_of_isFinite`: the pullback of an ample invertible module
  along a finite morphism is ample, which is what makes the left-hand side of the source's
  statement a degree without a hypothesis.
* `AlgebraicGeometry.intersectionNumber_eq_intersectionNumber_id`: the intersection number
  against a closed subscheme whose immersion is an isomorphism is the intersection number
  against `X` itself.  This is what turns the scheme-theoretic image of a dominant morphism to a
  variety back into the variety.
* `AlgebraicGeometry.degreeOver_eq_degreeOver_of_isIso`: the degree of a dominant morphism is
  unchanged by composing with an isomorphism, which is what turns `deg(Y/f(Y))` into `deg(Y/X)`.
* `AlgebraicGeometry.surjective_of_isIntegralHom_of_isDominant`: an integral dominant morphism is
  surjective, which is what makes `f(Y) = X` and `dim Y = dim X`.

## Implementation notes

**The route is the source's.**  [Stacks, Tag 0BET], available here as
`AlgebraicGeometry.intersectionNumber_pullback_eq_degreeOver_mul`, is the same formula for an
integral closed subscheme `Z ⊂ Y` and the scheme-theoretic image `f(Z)`; Tag 0BEX is its case
`Z = Y`, where the image is the whole of `X`.  Three things have to be said to read it that way,
and they are the three auxiliary results above: `f` is surjective, so `f(Y)` is `X` as a closed
subscheme and `dim Y = dim X` ([Stacks, Tag 0ECG]); the intersection number against `f(Y)` is
therefore the intersection number against `X`; and `deg(Y/f(Y))` is `deg(Y/X)`.

**Ampleness.**  The source states the formula for an ample `𝓛`, since that is where `deg_𝓛` is
called a degree.  Ampleness is used nowhere in the proof — neither side needs it to be formed,
as `AlgebraicGeometry.degreeWithRespectTo` is `AlgebraicGeometry.selfIntersectionNumber` with an
inert ampleness argument — so the work is done for an arbitrary invertible module and the
source's ample statement is read off from it.  It is read off with no hypothesis added: the
ampleness of `f^*𝓛` that the left-hand side needs is supplied, not assumed, by
`AlgebraicGeometry.isAmple_pullback_of_isFinite`, which is [Stacks, Tag 0892] part (2) for a
finite morphism.

**The dimension.**  The common dimension `d` is passed as a natural number together with
`topologicalKrullDim X = d`, exactly as in `AlgebraicGeometry.degreeWithRespectTo`: that
hypothesis is what makes `d` the source's `dim(X)`, and `d` is determined by `X`.  The dimension
of `Y` is then `d` as well, by surjectivity and integrality of `f`, and is not a second
hypothesis.

**Invariance of the intersection number.**  `AlgebraicGeometry.intersectionNumber` computes the
Euler characteristics on the subscheme, so moving from `f(Y)` to `X` is a comparison across an
isomorphism of schemes.  It is made on `X`, not upstairs: the projection formula
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion` turns each
Euler characteristic on the subscheme into one on `X` of a twist of the direct image of the
structure sheaf, and there the only comparison left is
`AlgebraicGeometry.pushforwardUnitIso`, that the direct image of the structure sheaf along an
isomorphism is the structure sheaf.

## References

* [Stacks Project, Tag 0BEX](https://stacks.math.columbia.edu/tag/0BEX)
* [Stacks Project, Tag 0BET](https://stacks.math.columbia.edu/tag/0BET)
* [Stacks Project, Tag 0BEW](https://stacks.math.columbia.edu/tag/0BEW)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
* [Stacks Project, Tag 0ECG](https://stacks.math.columbia.edu/tag/0ECG)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] twistedSheaf_isCoherent isCoherent_pushforward_of_isClosedImmersion
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent

/-! ### An integral dominant morphism is surjective -/

/-- **An integral dominant morphism of schemes is surjective.**  An integral morphism is closed,
so its range is a closed set; dominance says that range is dense, hence everything. -/
@[ega "IV 6.15.5" "more general"]
public theorem surjective_of_isIntegralHom_of_isDominant {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegralHom f] [IsDominant f] : Surjective f := by
  refine ⟨fun x => ?_⟩
  have hx := (isDominant_iff f).mp ‹IsDominant f› x
  rwa [f.isClosedMap.isClosed_range.closure_eq] at hx

/-- **A finite dominant morphism of schemes preserves the dimension.**  It is integral and, by
`AlgebraicGeometry.surjective_of_isIntegralHom_of_isDominant`, surjective, so this is
[Stacks, Tag 0ECG]. -/
@[ega "IV 5.4.1" "special case", ega "IV 5.4.2" "more general", ega "IV 5.6.6" "special case"]
public theorem topologicalKrullDim_eq_of_isFinite_of_isDominant {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsDominant f] : topologicalKrullDim Y = topologicalKrullDim X :=
  have := surjective_of_isIntegralHom_of_isDominant f
  topologicalKrullDim_eq_of_isIntegralHom_of_surjective f

/-- **The immersion of the scheme-theoretic image of a surjective morphism is surjective.** -/
public theorem surjective_imageι {Y X : Scheme.{u}} (g : Y ⟶ X) [Surjective g] :
    Surjective g.imageι := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := (surjective_iff g).mp inferInstance x
  exact ⟨g.toImage y, by rw [← Scheme.Hom.comp_apply, g.toImage_imageι]⟩

/-! ### The degree of a dominant morphism is unchanged by an isomorphism of the target -/

/-- Transporting a stalk map along an equality of its image point preserves bijectivity. -/
private theorem bijective_eqRec_stalkMap {Y X : Scheme.{u}} (f : Y ⟶ X) (y : Y) {x : X}
    (h : f.base y = x) (hb : Function.Bijective (f.stalkMap y).hom) :
    Function.Bijective ((h ▸ f.stalkMap y).hom) := by
  cases h
  exact hb

/-- **An isomorphism of integral schemes induces a bijection of function fields.**  The extension
of function fields is the stalk map at the generic point, transported along the identification of
its image with the generic point of the target, and the stalk map of an isomorphism is an
isomorphism. -/
public theorem bijective_dominantFunctionFieldMap_of_isIso {T X : Scheme.{u}} (ι : T ⟶ X)
    [IsIntegral T] [IsIntegral X] [IsDominant ι] [IsIso ι] :
    Function.Bijective (dominantFunctionFieldMap ι) := by
  unfold dominantFunctionFieldMap
  exact bijective_eqRec_stalkMap ι (genericPoint T) _
    (ConcreteCategory.bijective_of_isIso (ι.stalkMap (genericPoint T)))

/-- **The degree of a dominant morphism is unchanged by composing with an isomorphism**: if
`g ≫ ι = f` with `ι` an isomorphism, then `deg(Y/X) = deg(Y/T)`.

Both degrees are degrees of the extension of function fields induced by the morphism, and the two
extensions differ by the ring isomorphism of function fields that `ι` induces; the tower of the
two extensions commutes by the functoriality of the function-field map,
[Stacks, Tag 02JU]. -/
public theorem degreeOver_eq_degreeOver_of_isIso {Y T X : Scheme.{u}} (f : Y ⟶ X) (g : Y ⟶ T)
    (ι : T ⟶ X) (hf : g ≫ ι = f) [IsIntegral Y] [IsIntegral T] [IsIntegral X]
    [LocallyOfFiniteType g] [IsDominant g] [IsIso ι] [LocallyOfFiniteType f] [IsDominant f] :
    degreeOver f = degreeOver g := by
  subst hf
  let : IsDominant ι := (isDominant_iff ι).mpr
    (Function.Surjective.denseRange (ι.homeomorph.surjective))
  let : Algebra T.functionField Y.functionField := (dominantFunctionFieldMap g).toAlgebra
  let : Algebra X.functionField Y.functionField :=
    (dominantFunctionFieldMap (g ≫ ι)).toAlgebra
  rw [degreeOver_eq_finrank (g ≫ ι) rfl, degreeOver_eq_finrank g rfl]
  refine Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective (dominantFunctionFieldMap ι)
      (bijective_dominantFunctionFieldMap_of_isIso ι)) (RingEquiv.refl Y.functionField) ?_
  exact (Stacks.Chow.dominantFunctionFieldMap_comp g ι).symm

/-! ### The intersection number against a subscheme isomorphic to the whole scheme -/

/-- **The intersection number against a closed subscheme whose immersion is an isomorphism is the
intersection number against the scheme itself**:
`(𝓛_1 ⋯ 𝓛_d · W) = (𝓛_1 ⋯ 𝓛_d · X)` for `j : W ⟶ X` a closed immersion which is an
isomorphism.

The intersection number is the mixed finite difference of Euler characteristics computed on the
subscheme.  Each of them is moved onto `X` by the projection formula
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`, where it
becomes the Euler characteristic of a twist of `j_*𝒪_W`; there `j_*𝒪_W ≅ 𝒪_X ≅ (𝟙_X)_*𝒪_X` by
`AlgebraicGeometry.pushforwardUnitIso`, and the Euler characteristic is an isomorphism invariant.
-/
public theorem intersectionNumber_eq_intersectionNumber_id (k : Type u) [Field k]
    {X W : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [IsLocallyNoetherian X]
    (j : W ⟶ X) [IsClosedImmersion j] [IsIso j] (d : ℕ)
    (hW : topologicalKrullDim W ≤ (d : WithBot ℕ∞))
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)] :
    intersectionNumber k p j d hW L = intersectionNumber k p (𝟙 X) d hX L := by
  have : IsLocallyNoetherian W := isLocallyNoetherian_of_isClosedImmersion j
  rw [intersectionNumber_eq_sum_eulerCharacteristic,
    intersectionNumber_eq_sum_eulerCharacteristic]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  have hiso : (Scheme.Modules.pushforward j).obj (SheafOfModules.unit W.ringCatSheaf) ≅
      (Scheme.Modules.pushforward (𝟙 X)).obj (SheafOfModules.unit X.ringCatSheaf) :=
    pushforwardUnitIso j ≪≫ ((Scheme.Modules.pushforwardId X).app _).symm
  have hup := @eulerCharacteristic_eq_of_iso k _ X p _
    (twistedSheaf ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit W.ringCatSheaf)) L
      (fun i => if i ∈ T then 1 else 0))
    (twistedSheaf ((Scheme.Modules.pushforward (𝟙 X)).obj (SheafOfModules.unit X.ringCatSheaf)) L
      (fun i => if i ∈ T then 1 else 0))
    inferInstance inferInstance
    (twistedSheafIsoOfIso L hiso (fun i => if i ∈ T then 1 else 0))
  have push : ∀ {V : Scheme.{u}} (g : V ⟶ X) [IsClosedImmersion g]
      [IsLocallyNoetherian V], _ = _ := fun g =>
    eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k g p L
      (SheafOfModules.unit _) (fun i => if i ∈ T then 1 else 0) inferInstance
      (isCoherent_twistedSheafUnitPullback k p g L fun i => if i ∈ T then 1 else 0)
  exact (push j).symm.trans (hup.trans (push (𝟙 X)))

/-! ### Stacks Tag 0BEX -/

/-- **[Stacks, Tag 0BEX].** Let `k` be a field, let `f : Y ⟶ X` be a finite dominant morphism of
proper varieties over `k` of dimension `d` and let `𝓛` be an invertible `𝒪_X`-module.  Then

`(f^*𝓛^d · Y) = deg(f) (𝓛^d · X)`,

the degree `deg(f) = [R(Y) : R(X)]` being `AlgebraicGeometry.degreeOver` of
[Stacks, Morphisms, Definition 02NY].  For `𝓛` ample both sides are the degrees
`deg_{f^*𝓛}(Y)` and `deg_𝓛(X)` of [Stacks, Tag 0BEW], which is the source's statement; see
`AlgebraicGeometry.degreeWithRespectTo_pullback_of_isFinite`.

Ampleness is not assumed: it is not used by the source's proof and neither side needs it to be
formed. -/
@[stacks 0BEX "for an arbitrary invertible module, with no ampleness"]
public theorem selfIntersectionNumber_pullback_of_isFinite (k : Type u) [Field k]
    {Y X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety k p] [IsProper p] (f : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsVariety k (f ≫ p)] (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    selfIntersectionNumber k (f ≫ p) (𝟙 Y) d
          (((topologicalKrullDim_eq_of_isFinite_of_isDominant f).trans hd).le)
          ((Scheme.Modules.pullback f).obj L) =
      (degreeOver f : ℤ) * selfIntersectionNumber k p (𝟙 X) d hd.le L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hdY : topologicalKrullDim Y = (d : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_of_isFinite_of_isDominant f).trans hd
  -- the scheme-theoretic image of `𝟙 Y ≫ f` is the whole of `X`
  have : Surjective (𝟙 Y ≫ f) := by
    rw [Category.id_comp]; exact surjective_of_isIntegralHom_of_isDominant f
  have : Surjective (𝟙 Y ≫ f).imageι := surjective_imageι (𝟙 Y ≫ f)
  have : IsIso (𝟙 Y ≫ f).imageι :=
    isIso_of_isClosedImmersion_of_surjective (𝟙 Y ≫ f).imageι
  have : IsIntegral (𝟙 Y ≫ f).image := Stacks.Chow.isIntegral_image (𝟙 Y ≫ f)
  have : IsProper (𝟙 Y ≫ f).toImage := Stacks.Chow.isProper_toImage (𝟙 Y ≫ f)
  have hIm : topologicalKrullDim (𝟙 Y ≫ f).image = (d : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq (𝟙 Y ≫ f).imageι
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(𝟙 Y ≫ f).imageι.isEmbedding, (𝟙 Y ≫ f).imageι.surjective⟩)).trans hd
  -- Tag 0BET at the integral closed subscheme `𝟙 Y ⊂ Y`
  have hpull := intersectionNumber_pullback_eq_degreeOver_mul k (f ≫ p) p f rfl (𝟙 Y) d hdY
    (fun _ : Fin d => L) hIm
  have hdeg : degreeOver f = degreeOver (𝟙 Y ≫ f).toImage :=
    degreeOver_eq_degreeOver_of_isIso f (𝟙 Y ≫ f).toImage (𝟙 Y ≫ f).imageι
      ((𝟙 Y ≫ f).toImage_imageι.trans (Category.id_comp f))
  have hint : intersectionNumber k p (𝟙 Y ≫ f).imageι d hIm.le (fun _ : Fin d => L) =
      intersectionNumber k p (𝟙 X) d hd.le (fun _ : Fin d => L) :=
    intersectionNumber_eq_intersectionNumber_id k p (𝟙 Y ≫ f).imageι d hIm.le hd.le _
  rw [selfIntersectionNumber_eq_intersectionNumber, selfIntersectionNumber_eq_intersectionNumber,
    hpull, hdeg, hint]

/-! ### Stacks Tag 0BEX, the source's ample statement -/

/-- **The pullback of an ample invertible module along a finite morphism is ample**, at the
`AlgebraicGeometry.Scheme.Modules.IsAmple` spelling of [Stacks, Tag 01PS].

This is [Stacks, Tag 0892] part (2) for a finite — hence affine — morphism, proved as
`Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite` at the `Stacks.Ample.IsAmple`
spelling of the same tag, read across the comparison of the two spellings
`Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple`.  No attribute is attached: Tag 0892 is
already carried where it is proved. -/
public theorem isAmple_pullback_of_isFinite {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    Scheme.Modules.IsAmple Y ((Scheme.Modules.pullback f).obj L) :=
  (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple Y _).mpr
    (Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite f L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mp hL))

/-- **[Stacks, Tag 0BEX].** Let `k` be a field, let `f : Y ⟶ X` be a finite dominant morphism of
proper varieties over `k` and let `𝓛` be an ample invertible `𝒪_X`-module.  Then

`deg_{f^*𝓛}(Y) = deg(f) deg_𝓛(X)`,

the degrees being those of [Stacks, Tag 0BEW] and `deg(f) = [R(Y) : R(X)]` that of
[Stacks, Morphisms, Definition 02NY].

The dimension of `X` is passed as a natural number `d` together with
`topologicalKrullDim X = d`, as `AlgebraicGeometry.degreeWithRespectTo` asks; the dimension of
`Y` is then `d` too and is not a hypothesis.  Neither is the ampleness of `f^*𝓛` that the
left-hand side needs: it is `AlgebraicGeometry.isAmple_pullback_of_isFinite`.

The content is `AlgebraicGeometry.selfIntersectionNumber_pullback_of_isFinite`, which does not
mention ampleness; `AlgebraicGeometry.degreeWithRespectTo` is by definition the
self-intersection number, so this is that statement read at the source's notation. -/
@[stacks 0BEX]
public theorem degreeWithRespectTo_pullback_of_isFinite (k : Type u) [Field k]
    {Y X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety k p] [IsProper p] (f : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsVariety k (f ≫ p)] (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    degreeWithRespectTo k (f ≫ p) (𝟙 Y) d
          ((topologicalKrullDim_eq_of_isFinite_of_isDominant f).trans hd)
          ((Scheme.Modules.pullback f).obj L) (isAmple_pullback_of_isFinite f L hL) =
      (degreeOver f : ℤ) * degreeWithRespectTo k p (𝟙 X) d hd L hL :=
  selfIntersectionNumber_pullback_of_isFinite k p f d hd L

end AlgebraicGeometry

end
