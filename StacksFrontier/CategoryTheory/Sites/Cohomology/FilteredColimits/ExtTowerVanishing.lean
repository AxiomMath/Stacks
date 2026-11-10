module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Killing an `Ext` class along a tower of short exact sequences

Let `A` be an abelian category, let `Y` be an object of `A`, and let

```text
0 ⟶ Z (i+1) ⟶ P i ⟶ Z i ⟶ 0
```

be a tower of short exact sequences indexed by `i : ℕ` — the shape produced by the opcycles of a
resolution. This file proves that a class `e : Ext^(n+1) (Z 0) Y` vanishes as soon as

* `e` dies after restriction to `P 0`;
* `Ext^q (P i) Y = 0` whenever `i, q > 0` and `i + q = n + 1` (the off-diagonal vanishing);
* every map `Z (n+1) ⟶ Y` extends along `Z (n+1) ⟶ P n` (the one extension that has to be
  produced by hand, at the end of the tower).

That is `ext_eq_zero_of_exact_tower`: a dévissage which walks the class down the tower, shifting
the tower by one at each step, and in which the two vanishing inputs are exactly those supplied by
the cohomological hypotheses of Stacks 0GN3.

The extension input is in turn supplied, when `Y` is a filtered colimit of injective objects, by
`exists_extension_of_opcycles_filtered_colimit`: a map out of `Z (n+1) = X.opcycles (n+1)` into
such a colimit factors through a finite stage, because `Hom(X_{n+1}, -)` and `Hom(X_{n+2}, -)`
commute with the colimit, and once at a stage it extends by injectivity.

## Main results

* `Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_exact_tower`: the dévissage.
* `Stacks.Cohomology.ColimitsOfCohomology.exists_extension_of_opcycles_filtered_colimit`: a map
  from the opcycles of a chain complex to a filtered colimit of injective objects extends to the
  preceding term, provided the complex is exact there and `Hom` out of the two neighbouring terms
  commutes with the colimit.
* `Stacks.Cohomology.ColimitsOfCohomology.shortExact_opcycles_of_exactAt`: the short exact
  sequence `0 ⟶ opcycles (i+1) ⟶ X i ⟶ opcycles i ⟶ 0` attached to a chain complex which is
  exact in degree `i + 1`, which is what puts a resolution into the shape above.
* `Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_iso_first`: vanishing of `Ext` out of an
  object transports along an isomorphism of that object.
* `Stacks.Cohomology.ColimitsOfCohomology.isZero_extFunctorObj_colimit_of_injective`: `Ext` in a
  positive degree vanishes on a filtered colimit of injective objects as soon as it commutes with
  that colimit, which is how the off-diagonal vanishing input of the dévissage is obtained.

Injectivity of the stages is stronger than any of this needs, and the three statements below
weaken it to what the proofs consume. In
`exists_extension_of_cokernel_filtered_colimit_of_extension` and
`exists_extension_of_opcycles_filtered_colimit_of_extension` the stages are asked only for the one
extension the argument performs; in `isZero_extFunctorObj_colimit_of_isZero` only for the vanishing
that injectivity was used to produce. The extension hypothesis is then itself a vanishing
statement, by `exists_extension_of_exact_tower_of_ext_eq_zero`: along a tower of short exact
sequences the obstruction `Ext^1 (Z (n+1), Y)` to extending a map out of the top is
`Ext^(n+1) (Z 0, Y)`, so a `Y` which is merely *acyclic* against the tower — rather than
injective — supports the dévissage.

* `Stacks.Cohomology.ColimitsOfCohomology`
  `.exists_extension_of_cokernel_filtered_colimit_of_extension`
* `Stacks.Cohomology.ColimitsOfCohomology`
  `.exists_extension_of_opcycles_filtered_colimit_of_extension`
* `Stacks.Cohomology.ColimitsOfCohomology.isZero_extFunctorObj_colimit_of_isZero`
* `Stacks.Cohomology.ColimitsOfCohomology.exists_extension_of_exact_tower_of_ext_eq_zero`

## Implementation notes

`Hom`-sets are handled through `CategoryTheory.preadditiveCoyoneda`, whose values are abelian
groups, so that "a map into a filtered colimit comes from a stage" is literally the concreteness
of filtered colimits of abelian groups (`CategoryTheory.Limits.Concrete.colimit_exists_rep` and
`CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq`) transported along the comparison map
`colimit.post`. Accordingly the ambient category is taken at the universe convention
`A : Type (u + 1)` with `Category.{u} A`, which is the convention of a category of sheaves of
`u`-small abelian groups on a `u`-small site.

The induction in `ext_eq_zero_of_exact_tower` generalises the tower itself, not the degree alone:
at the inductive step the tower is replaced by its shift `i ↦ Z (i + 1)`, `i ↦ P (i + 1)`, which
is what keeps the extension hypothesis — a statement about the far end of the tower — unchanged.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.ColimitsOfCohomology

/-! ### The opcycles tower of a chain complex -/

/-- In a chain complex the canonical map out of the opcycles in degree `i + 1`, followed by the
canonical map onto the opcycles in degree `i`, is zero: both are detected after precomposition
with the epimorphism `X (i+1) ⟶ opcycles (i+1)`, where the composite is `d ≫ pOpcycles`. -/
public lemma fromOpcycles_comp_pOpcycles {A : Type*} [Category* A] [Abelian A]
    (X : ChainComplex A ℕ) (i : ℕ) :
    X.fromOpcycles (i + 1) i ≫ X.pOpcycles i = 0 := by
  apply (cancel_epi (X.pOpcycles (i + 1))).1
  rw [← Category.assoc, X.p_fromOpcycles, X.d_pOpcycles, comp_zero]

/-- **The opcycles tower.** If a chain complex `X` is exact in degree `i + 1`, then

```text
0 ⟶ X.opcycles (i+1) ⟶ X i ⟶ X.opcycles i ⟶ 0
```

is short exact. Exactness gives both halves: the right-hand map is the cokernel of the
differential `X (i+1) ⟶ X i`, through which the left-hand map factors by an epimorphism, and the
left-hand map is a monomorphism because exactness at `i + 1` says precisely that the map from the
opcycles into the next term is injective. -/
public lemma shortExact_opcycles_of_exactAt {A : Type*} [Category* A] [Abelian A]
    (X : ChainComplex A ℕ) (i : ℕ) (hX : X.ExactAt (i + 1)) :
    (ShortComplex.mk (X.fromOpcycles (i + 1) i) (X.pOpcycles i)
      (fromOpcycles_comp_pOpcycles X i)).ShortExact := by
  let S := ShortComplex.mk (X.fromOpcycles (i + 1) i) (X.pOpcycles i)
    (fromOpcycles_comp_pOpcycles X i)
  have hExact : S.Exact := by
    apply S.exact_of_g_is_cokernel
    exact isCokernelOfComp (X.pOpcycles (i + 1)) (X.d (i + 1) i)
      (X.opcyclesIsCokernel (i + 1) i (by simp)) S.zero
      (X.p_fromOpcycles (i + 1) i)
  have hMono : Mono S.f := by
    change Mono (X.fromOpcycles (i + 1) i)
    have hi : (ComplexShape.down ℕ).prev (i + 1) = i + 2 := by simp
    have hj : (ComplexShape.down ℕ).next (i + 1) = i := by simp
    have he : (X.sc' (i + 2) (i + 1) i).Exact :=
      (X.exactAt_iff' (i + 2) (i + 1) i hi hj).1 hX
    have hm : Mono (X.sc' (i + 2) (i + 1) i).fromOpcycles := he.mono_fromOpcycles
    rw [← X.opcyclesIsoSc'_inv_fromOpcycles (i + 2) (i + 1) i hi hj] at hm
    exact (mono_comp_iff_of_isIso _ _).mp hm
  exact ShortComplex.ShortExact.mk' hExact hMono inferInstance

/-! ### Maps into a filtered colimit -/

section FilteredColimit

variable {A : Type (u + 1)} [Category.{u} A] [Abelian A]
  {I : Type u} [SmallCategory I] [IsFiltered I]

/-- A map into a filtered colimit factors through a finite stage, provided `Hom(X, -)` commutes
with that colimit. The comparison map `colimit.post` is an isomorphism of abelian groups, so the
statement is the concreteness of filtered colimits of abelian groups. -/
public lemma hom_to_filtered_colimit_exists_stage (X : A) (F : I ⥤ A) [HasColimit F]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op X)))] (a : X ⟶ colimit F) :
    ∃ (i : I) (b : X ⟶ F.obj i), b ≫ colimit.ι F i = a := by
  let H := preadditiveCoyoneda.obj (op X)
  let t := colimit.post F H
  obtain ⟨i, b, hb⟩ := Concrete.colimit_exists_rep (F ⋙ H) (inv t a)
  refine ⟨i, b, ?_⟩
  have hpost (j : I) (c : X ⟶ F.obj j) :
      t ((colimit.ι (F ⋙ H) j) c) = c ≫ colimit.ι F j :=
    ConcreteCategory.congr_hom (colimit.ι_post F H j) c
  have hinv : t (inv t a) = a := ConcreteCategory.congr_hom (IsIso.inv_hom_id t) a
  exact (hpost i b).symm.trans ((congrArg (fun z => t z) hb).trans hinv)

/-- A map to a stage of a filtered colimit which becomes zero in the colimit is already zero
after passing to a later stage, provided `Hom(X, -)` commutes with the colimit. -/
public lemma hom_to_filtered_colimit_zero_at_stage (X : A) (F : I ⥤ A) [HasColimit F]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op X)))]
    {i : I} (a : X ⟶ F.obj i) (ha : a ≫ colimit.ι F i = 0) :
    ∃ (j : I) (φ : i ⟶ j), a ≫ F.map φ = 0 := by
  let H := preadditiveCoyoneda.obj (op X)
  let t := colimit.post F H
  have hpost (j : I) (c : X ⟶ F.obj j) :
      t ((colimit.ι (F ⋙ H) j) c) = c ≫ colimit.ι F j :=
    ConcreteCategory.congr_hom (colimit.ι_post F H j) c
  have h : (colimit.ι (F ⋙ H) i) a = (colimit.ι (F ⋙ H) i) 0 := by
    apply (ConcreteCategory.bijective_of_isIso t).1
    apply (hpost i a).trans
    rw [ha]
    have hz := (hpost i (0 : X ⟶ F.obj i)).symm
    change (0 : X ⟶ F.obj i) ≫ colimit.ι F i = t ((colimit.ι (F ⋙ H) i) 0) at hz
    change (0 : X ⟶ colimit F) = t ((colimit.ι (F ⋙ H) i) 0)
    simpa only [zero_comp] using hz
  obtain ⟨j, φ, ψ, hφψ⟩ := Concrete.colimit_exists_of_rep_eq (F ⋙ H) a (0 : X ⟶ F.obj i) h
  refine ⟨j, φ, ?_⟩
  exact hφψ.trans (H.map (F.map ψ)).hom.map_zero

/-- Core of the extension lemmas for cokernels: if maps from the cokernel into each stage extend
along `m`, so do maps from the cokernel into the colimit. -/
private lemma exists_extension_of_cokernel_filtered_colimit_aux
    {P Q R : A} (d : P ⟶ Q) (m : cokernel d ⟶ R)
    (F : I ⥤ A) [HasColimit F]
    (hF : ∀ j, ∀ c : cokernel d ⟶ F.obj j, ∃ v : R ⟶ F.obj j, m ≫ v = c)
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op P)))]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op Q)))]
    (a : cokernel d ⟶ colimit F) :
    ∃ b : R ⟶ colimit F, m ≫ b = a := by
  obtain ⟨i, b, hb⟩ := hom_to_filtered_colimit_exists_stage Q F (cokernel.π d ≫ a)
  have hz : (d ≫ b) ≫ colimit.ι F i = 0 := by
    rw [Category.assoc, hb, ← Category.assoc, cokernel.condition, zero_comp]
  obtain ⟨j, φ, hφ⟩ := hom_to_filtered_colimit_zero_at_stage P F (d ≫ b) hz
  let b' : Q ⟶ F.obj j := b ≫ F.map φ
  have hbd : d ≫ b' = 0 := by simpa only [b', Category.assoc] using hφ
  let c : cokernel d ⟶ F.obj j := cokernel.desc d b' hbd
  have hc : c ≫ colimit.ι F j = a := by
    apply (cancel_epi (cokernel.π d)).1
    calc
      cokernel.π d ≫ c ≫ colimit.ι F j = b' ≫ colimit.ι F j := by
        dsimp [c]
        rw [← Category.assoc, cokernel.π_desc]
      _ = b ≫ colimit.ι F i := by dsimp [b']; rw [Category.assoc, colimit.w]
      _ = cokernel.π d ≫ a := hb
  obtain ⟨v, hv⟩ := hF j c
  exact ⟨v ≫ colimit.ι F j, by rw [← Category.assoc, hv, hc]⟩

/-- A map from a cokernel into a filtered colimit of injective objects extends along any
monomorphism out of that cokernel, provided `Hom` out of the two terms of the presented map
commutes with the colimit.

The map is pushed to a stage, where the relation defining the cokernel holds after moving one
step further in the index category, so that it descends to the cokernel at that stage; there the
stage is injective and the extension exists. -/
public lemma exists_extension_of_cokernel_filtered_colimit
    {P Q R : A} (d : P ⟶ Q) (m : cokernel d ⟶ R) [Mono m]
    (F : I ⥤ A) [HasColimit F] (hF : ∀ i, Injective (F.obj i))
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op P)))]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op Q)))]
    (a : cokernel d ⟶ colimit F) :
    ∃ b : R ⟶ colimit F, m ≫ b = a := by
  exact exists_extension_of_cokernel_filtered_colimit_aux d m F
    (fun j c => haveI := hF j; Injective.factors c m) a

/-- `exists_extension_of_cokernel_filtered_colimit` with injectivity of the stages weakened to the
property the proof actually uses: that a map from the cokernel *into a stage* extends along `m`.
Injectivity is applied there to the single monomorphism `m` and to nothing else, so this is the
weakest hypothesis which still runs the argument — and `m` need not be a monomorphism at all.

The map is pushed to a stage exactly as in `exists_extension_of_cokernel_filtered_colimit`; only
the final lifting step differs, applying `hF` in place of `CategoryTheory.Injective.factors`. -/
public lemma exists_extension_of_cokernel_filtered_colimit_of_extension
    {P Q R : A} (d : P ⟶ Q) (m : cokernel d ⟶ R)
    (F : I ⥤ A) [HasColimit F]
    (hF : ∀ j, ∀ c : cokernel d ⟶ F.obj j, ∃ v : R ⟶ F.obj j, m ≫ v = c)
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op P)))]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op Q)))]
    (a : cokernel d ⟶ colimit F) :
    ∃ b : R ⟶ colimit F, m ≫ b = a := by
  exact exists_extension_of_cokernel_filtered_colimit_aux d m F hF a

/-- Core of the extension lemmas for opcycles: the extension property at each stage gives the
extension into the colimit. -/
private lemma exists_extension_of_opcycles_filtered_colimit_aux
    (X : ChainComplex A ℕ) (i : ℕ)
    (F : I ⥤ A) [HasColimit F]
    (hF : ∀ j, ∀ c : X.opcycles (i + 1) ⟶ F.obj j,
      ∃ v : X.X i ⟶ F.obj j, X.fromOpcycles (i + 1) i ≫ v = c)
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op (X.X (i + 1)))))]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op (X.X (i + 2)))))]
    (a : X.opcycles (i + 1) ⟶ colimit F) :
    ∃ b : X.X i ⟶ colimit F, X.fromOpcycles (i + 1) i ≫ b = a := by
  have hi : (ComplexShape.down ℕ).prev (i + 1) = i + 2 := by simp
  let d := X.d (i + 2) (i + 1)
  let E : X.opcycles (i + 1) ≅ cokernel d :=
    X.opcyclesIsoSc' (i + 2) (i + 1) i hi (by simp) ≪≫
      (X.sc' (i + 2) (i + 1) i).opcyclesIsoCokernel
  obtain ⟨b, hb⟩ := exists_extension_of_cokernel_filtered_colimit_of_extension
    d (E.inv ≫ X.fromOpcycles (i + 1) i) F
    (fun j c => by
      obtain ⟨v, hv⟩ := hF j (E.hom ≫ c)
      exact ⟨v, by rw [Category.assoc, hv, ← Category.assoc, E.inv_hom_id, Category.id_comp]⟩)
    (E.inv ≫ a)
  refine ⟨b, ?_⟩
  have h := congrArg (fun z => E.hom ≫ z) hb
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

/-- **The extension input of the dévissage.** Let `X` be a chain complex which is exact in degree
`i + 1` and let `F` be a filtered diagram of injective objects such that `Hom` out of `X (i+1)`
and out of `X (i+2)` commutes with its colimit. Then every map `X.opcycles (i+1) ⟶ colimit F`
extends along `X.opcycles (i+1) ⟶ X i`.

The opcycles in degree `i + 1` are the cokernel of the differential `X (i+2) ⟶ X (i+1)`, and the
map down to `X i` is a monomorphism by exactness, so this is
`exists_extension_of_cokernel_filtered_colimit`. -/
public lemma exists_extension_of_opcycles_filtered_colimit
    (X : ChainComplex A ℕ) (i : ℕ) (hX : X.ExactAt (i + 1))
    (F : I ⥤ A) [HasColimit F] (hF : ∀ j, Injective (F.obj j))
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op (X.X (i + 1)))))]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op (X.X (i + 2)))))]
    (a : X.opcycles (i + 1) ⟶ colimit F) :
    ∃ b : X.X i ⟶ colimit F, X.fromOpcycles (i + 1) i ≫ b = a := by
  have : Mono (X.fromOpcycles (i + 1) i) := (shortExact_opcycles_of_exactAt X i hX).mono_f
  exact exists_extension_of_opcycles_filtered_colimit_aux X i F
    (fun j c => haveI := hF j; Injective.factors c _) a

/-- `exists_extension_of_opcycles_filtered_colimit` with injectivity of the stages weakened to the
extension property at each stage. Exactness of `X` at `i + 1` is not needed either: it entered the
injective version only to make the map down to `X i` a monomorphism, which
`exists_extension_of_cokernel_filtered_colimit_of_extension` no longer asks for. -/
public lemma exists_extension_of_opcycles_filtered_colimit_of_extension
    (X : ChainComplex A ℕ) (i : ℕ)
    (F : I ⥤ A) [HasColimit F]
    (hF : ∀ j, ∀ c : X.opcycles (i + 1) ⟶ F.obj j,
      ∃ v : X.X i ⟶ F.obj j, X.fromOpcycles (i + 1) i ≫ v = c)
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op (X.X (i + 1)))))]
    [IsIso (colimit.post F (preadditiveCoyoneda.obj (op (X.X (i + 2)))))]
    (a : X.opcycles (i + 1) ⟶ colimit F) :
    ∃ b : X.X i ⟶ colimit F, X.fromOpcycles (i + 1) i ≫ b = a := by
  exact exists_extension_of_opcycles_filtered_colimit_aux X i F hF a

omit [IsFiltered I] in
/-- `isZero_extFunctorObj_colimit_of_injective` with injectivity of the stages weakened to the
vanishing it is used for: injectivity enters that proof only through
`CategoryTheory.Abelian.Ext.subsingleton_of_injective`, so pointwise vanishing of the same `Ext`
group is all the argument consumes. The degree is left arbitrary, since positivity was only there
to make injectivity bite. -/
public lemma isZero_extFunctorObj_colimit_of_isZero [HasExt.{u} A] (X : A) (q : ℕ)
    (F : I ⥤ A) [HasColimit F] (hF : ∀ i, IsZero ((Abelian.extFunctorObj.{u} X q).obj (F.obj i)))
    [IsIso (colimit.post F (Abelian.extFunctorObj.{u} X q))] :
    IsZero ((Abelian.extFunctorObj.{u} X q).obj (colimit F)) := by
  let H := Abelian.extFunctorObj.{u} X q
  have := preservesColimit_of_isIso_post H F
  exact (isColimitOfPreserves H (colimit.isColimit F)).isZero_pt ((Functor.isZero_iff _).2 hF)

omit [IsFiltered I] in
/-- **`Ext` vanishes on a filtered colimit of injective objects**, in every positive degree in
which it commutes with that colimit: the colimit of the diagram `Ext^(q+1)(X, F -)` is then the
value on the colimit, and every term of that diagram is zero because `F i` is injective. -/
public lemma isZero_extFunctorObj_colimit_of_injective [HasExt.{u} A] (X : A) (q : ℕ)
    (F : I ⥤ A) [HasColimit F] (hF : ∀ i, Injective (F.obj i))
    [IsIso (colimit.post F (Abelian.extFunctorObj.{u} X (q + 1)))] :
    IsZero ((Abelian.extFunctorObj.{u} X (q + 1)).obj (colimit F)) := by
  let H := Abelian.extFunctorObj.{u} X (q + 1)
  have := preservesColimit_of_isIso_post H F
  apply (isColimitOfPreserves H (colimit.isColimit F)).isZero_pt
  rw [Functor.isZero_iff]
  intro i
  have := hF i
  have : Subsingleton (Abelian.Ext.{u} X (F.obj i) (q + 1)) :=
    Abelian.Ext.subsingleton_of_injective X (F.obj i) q
  change IsZero (AddCommGrpCat.of (Abelian.Ext.{u} X (F.obj i) (q + 1)))
  exact AddCommGrpCat.isZero_of_subsingleton _

end FilteredColimit

/-! ### The dévissage -/

/-- Vanishing of `Ext` out of an object transports along an isomorphism of that object. -/
public lemma ext_eq_zero_of_iso_first {A : Type*} [Category* A] [Abelian A] [HasExt.{u} A]
    {X X' Y : A} (e : X ≅ X') (q : ℕ)
    (h : ∀ a : Abelian.Ext.{u} X' Y q, a = 0) (a : Abelian.Ext.{u} X Y q) : a = 0 := by
  have hz := h ((Abelian.Ext.mk₀ e.inv).comp a (zero_add q))
  have hz' := congrArg
    (fun b : Abelian.Ext.{u} X' Y q => (Abelian.Ext.mk₀ e.hom).comp b (zero_add q)) hz
  simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Abelian.Ext.mk₀_id_comp,
    Abelian.Ext.comp_zero] using hz'

/-- **Dévissage along a tower of short exact sequences.** Let

```text
0 ⟶ Z (i+1) --f i--> P i --g i--> Z i ⟶ 0
```

be short exact for every `i : ℕ`, and let `Y` be an object. A class `e` in `Ext^(n+1) (Z 0) Y`
vanishes as soon as

* `(g 0)^* e = 0`;
* `Ext^q (P i) Y = 0` whenever `i, q > 0` and `i + q = n + 1`;
* every map `Z (n+1) ⟶ Y` extends along `f n`.

The contravariant long exact sequence of the `i = 0` row writes `e` as the Yoneda product of the
extension class of that row with a class `a` in `Ext^n (Z 1) Y`. For `n = 0` such a class is a
map, which the extension hypothesis factors through `f 0`, making the product vanish. For `n > 0`
the same hypotheses hold for the shifted tower and one degree lower, so `a = 0` by induction;
the off-diagonal vanishing enters as the hypothesis `Ext^(n+1) (P 1) Y = 0` needed at the base of
the shifted tower. -/
public lemma ext_eq_zero_of_exact_tower {A : Type*} [Category* A] [Abelian A] [HasExt.{u} A]
    (Z P : ℕ → A) (f : ∀ i, Z (i + 1) ⟶ P i) (g : ∀ i, P i ⟶ Z i)
    (hz : ∀ i, f i ≫ g i = 0)
    (hs : ∀ i, (ShortComplex.mk (f i) (g i) (hz i)).ShortExact)
    (Y : A) (n : ℕ)
    (hv : ∀ i q, 0 < i → 0 < q → i + q = n + 1 → ∀ e : Abelian.Ext.{u} (P i) Y q, e = 0)
    (hext : ∀ a : Z (n + 1) ⟶ Y, ∃ b : P n ⟶ Y, f n ≫ b = a)
    (e : Abelian.Ext.{u} (Z 0) Y (n + 1))
    (he : (Abelian.Ext.mk₀ (g 0)).comp e (zero_add _) = 0) : e = 0 := by
  induction n generalizing Z P with
  | zero =>
      obtain ⟨a, ha⟩ := Abelian.Ext.contravariant_sequence_exact₃ (hs 0) Y e he
        (show 1 + 0 = 1 from rfl)
      obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 a
      obtain ⟨b, hb⟩ := hext a
      rw [← hb, ← Abelian.Ext.mk₀_comp_mk₀, (hs 0).extClass_comp_assoc] at ha
      exact ha.symm
  | succ n ih =>
      obtain ⟨a, ha⟩ := Abelian.Ext.contravariant_sequence_exact₃ (hs 0) Y e he
        (show 1 + (n + 1) = n + 1 + 1 by omega)
      have ha0 : a = 0 := by
        apply ih (fun i => Z (i + 1)) (fun i => P (i + 1))
          (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => hz (i + 1))
          (fun i => hs (i + 1))
        · intro i q hi hq heq b
          exact hv (i + 1) q (by omega) hq (by omega) b
        · exact hext
        · exact hv 1 (n + 1) (by omega) (by omega) (by omega) _
      rw [ha0, Abelian.Ext.comp_zero] at ha
      exact ha.symm

/-- **The extension input of the dévissage, from acyclicity instead of injectivity.** Along a tower
of short exact sequences

```text
0 ⟶ Z (i+1) --f i--> P i --g i--> Z i ⟶ 0
```

every map `Z (n+1) ⟶ Y` extends along `f n` as soon as

* `Ext^q (P i, Y) = 0` for every `i` and every `q > 0`;
* `Ext^(n+1) (Z 0, Y) = 0`.

So the hypothesis `hext` of `ext_eq_zero_of_exact_tower` costs nothing beyond vanishing of `Ext`
against `Y`: it is the dimension shift `Ext^1 (Z (n+1), Y) ≅ Ext^(n+1) (Z 0, Y)` read off the
tower, where the first group is the obstruction to the extension.

The induction is on `n`, generalising the tower. At `n = 0` the contravariant long exact sequence
of the `i = 0` row reads `Hom(P 0, Y) ⟶ Hom(Z 1, Y) ⟶ Ext^1 (Z 0, Y)`, and the third group
vanishes, so the map comes from `P 0`. At `n + 1` the same sequence one degree up,
`Ext^(n+1) (P 0, Y) ⟶ Ext^(n+1) (Z 1, Y) ⟶ Ext^(n+2) (Z 0, Y)`, has both outer groups zero — the
first by the off-diagonal vanishing, the second by hypothesis — so `Ext^(n+1) (Z 1, Y) = 0` and the
shifted tower satisfies the same hypotheses one degree lower. -/
public lemma exists_extension_of_exact_tower_of_ext_eq_zero {A : Type*} [Category* A] [Abelian A]
    [HasExt.{u} A] (Z P : ℕ → A) (f : ∀ i, Z (i + 1) ⟶ P i) (g : ∀ i, P i ⟶ Z i)
    (hz : ∀ i, f i ≫ g i = 0)
    (hs : ∀ i, (ShortComplex.mk (f i) (g i) (hz i)).ShortExact)
    (Y : A) (n : ℕ)
    (hv : ∀ i q, 0 < q → ∀ e : Abelian.Ext.{u} (P i) Y q, e = 0)
    (hglob : ∀ e : Abelian.Ext.{u} (Z 0) Y (n + 1), e = 0)
    (a : Z (n + 1) ⟶ Y) : ∃ b : P n ⟶ Y, f n ≫ b = a := by
  induction n generalizing Z P with
  | zero =>
      obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₁ (hs 0) Y
        (Abelian.Ext.mk₀ a) (show 1 + 0 = 0 + 1 by omega) (hglob _)
      obtain ⟨b, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
      refine ⟨b, (Abelian.Ext.mk₀_bijective _ _).1 ?_⟩
      rw [← Abelian.Ext.mk₀_comp_mk₀]
      exact hx
  | succ n ih =>
      refine ih (fun i => Z (i + 1)) (fun i => P (i + 1)) (fun i => f (i + 1))
        (fun i => g (i + 1)) (fun i => hz (i + 1)) (fun i => hs (i + 1))
        (fun i q hq e => hv (i + 1) q hq e) (fun e => ?_) a
      obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₁ (hs 0) Y e
        (show 1 + (n + 1) = n + 1 + 1 by omega) (hglob _)
      rw [← hx, hv 0 (n + 1) (by omega) x, Abelian.Ext.comp_zero]

end Stacks.Cohomology.ColimitsOfCohomology

end
