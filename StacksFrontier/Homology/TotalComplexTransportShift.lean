module

public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp
public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# The transport of a total complex along a functor commutes with the shifts

Let `Φ : D ⥤ D'` be an additive functor carrying a bifunctor `F : A ⥤ B ⥤ D` to
`F' : A' ⥤ B' ⥤ D'` along additive `Φ₁ : A ⥤ A'` and `Φ₂ : B ⥤ B'`, by a degreewise comparison
`ε`.  `CategoryTheory.Functor.mapBifunctorTotalIso` is the resulting comparison of total cochain
complexes

`Φ(Tot(F(K, L))) ≅ Tot(F'(Φ₁K, Φ₂L))`.

This file proves that that comparison is compatible with the shift in each of the two variables,
against the isomorphisms `CochainComplex.mapBifunctorShift₁Iso` and
`CochainComplex.mapBifunctorShift₂Iso` of `Mathlib/Algebra/Homology/BifunctorShift.lean`.

## Main results

* `CategoryTheory.Functor.mapBifunctorTotalIso_commShift₁`: the compatibility in the first
  variable, where neither comparison carries a sign.
* `CategoryTheory.Functor.mapBifunctorTotalIso_commShift₂`: the compatibility in the second
  variable, where both carry the Koszul sign `(p * y).negOnePow` of
  `CochainComplex.ι_mapBifunctorShift₂Iso_hom_f`.
* `CategoryTheory.Functor.mapBifunctorTotalBifunctorIso`: the comparison in curried form, as an
  isomorphism of bifunctors on cochain complexes.
* `CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂`: **that isomorphism is a
  `CategoryTheory.NatTrans.CommShift₂Int`** — the shape in which the shift compatibility is
  consumed.
* `CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_hom_app_app` and
  `mapBifunctorTotalBifunctorIso_inv_app_app`: **its components are the comparisons it is
  assembled from** — what a consumer holding the same comparisons packaged on the product
  category needs in order to identify the two packagings without a `rfl` at the concrete
  bifunctor.

Together these are the datum the shift compatibility of the comparison of [Stacks, Tag 079U] on
K-flat representatives — `Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂` —
owes at its `pullbackTensorComplexNatIso` leg; see the implementation note there.

## Implementation notes

**Why the sign is not an obstruction.**  The Koszul sign of `mapBifunctorShift₂Iso` on the
summand indexed by `(p, q)` is `(p * y).negOnePow`, and it depends only on the first index and
the shift — not on the category.  So it is literally the same unit on both sides of the square,
and since `Φ` is additive it passes through `Φ.map` (`CategoryTheory.Functor.map_units_smul`).
What is left after cancelling it is `ι_mapBifunctorTotalIso_hom` on the summand `(p, q + y)`.
The first variable carries no sign at all and the proof is the same without that step.

**Why the proof runs on the `inv` of the comparison at the shifted pair.**  The source of both
sides of the square is `Φ` of a total complex, which is a coproduct only *because* `Φ` preserves
the antidiagonal coproducts, so extensionality does not apply to it directly; this is the same
asymmetry recorded in `StacksFrontier/Homology/TotalComplexTransport.lean`.  Moving the comparison
at the shifted pair to the other side by `CategoryTheory.Iso.inv_comp_eq` puts a genuine total
complex in source position, where `HomologicalComplex.mapBifunctor.hom_ext` applies, and the
factor that was moved is then consumed by `ι_mapBifunctorTotalIso_inv`.

**Why the index spellings have to be normalised before the identities are cancelled.**  The
summand of the shifted pair is indexed by `((Φ₁K).X p, (Φ₂(L⟦y⟧)).X q)`, and the commutation
isomorphism of `Φ₂.mapHomologicalComplex` lands in the *composite* spelling
`(Φ₂.mapHomologicalComplex _ ⋙ shiftFunctor _ y).obj L`.  A `CategoryTheory.Functor.map` whose
implicit source is `((shiftFunctor _ y).obj L).X q` while its argument is `𝟙 (L.X (q + y))` is
type-correct, but `CategoryTheory.Functor.map_id` does not match it — its two implicit objects
have to be *syntactically* equal.  Hence `Functor.comp_obj` is normalised away before the
rewrite that produces those identities, and the identities are then cancelled by `simp` rather
than by a keyed `rw`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

namespace CategoryTheory.Functor

universe vA vB vA' vB' uA uB uA' uB' v v' u u'

variable {A : Type uA} {B : Type uB} {D : Type u} {A' : Type uA'} {B' : Type uB'} {D' : Type u'}
  [Category.{vA} A] [Category.{vB} B] [Category.{v} D]
  [Category.{vA'} A'] [Category.{vB'} B'] [Category.{v'} D']
  [Preadditive A] [Preadditive B] [Preadditive D]
  [Preadditive A'] [Preadditive B'] [Preadditive D']
  (F : A ⥤ B ⥤ D) (F' : A' ⥤ B' ⥤ D')
  [F.Additive] [∀ X, (F.obj X).Additive]
  [F'.Additive] [∀ X, (F'.obj X).Additive]
  (Φ₁ : A ⥤ A') (Φ₂ : B ⥤ B') (Φ : D ⥤ D') [Φ₁.Additive] [Φ₂.Additive] [Φ.Additive]
  (ε : ∀ (a : A) (b : B), Φ.obj ((F.obj a).obj b) ≅ (F'.obj (Φ₁.obj a)).obj (Φ₂.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
    Φ.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (Φ₁.map f)).app (Φ₂.obj b))
  (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
    Φ.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (Φ₁.obj a)).map (Φ₂.map g))
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)]
  [∀ (K : CochainComplex A' ℤ) (L : CochainComplex B' ℤ),
    HomologicalComplex.HasMapBifunctor K L F' (ComplexShape.up ℤ)]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ)]
  [∀ n : ℤ, Limits.PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) Φ]

section Legs

variable (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)

/-- **The transport of a total complex commutes with the shift in the first variable.**
`CategoryTheory.Functor.mapBifunctorTotalIso` carries `CochainComplex.mapBifunctorShift₁Iso` for
`F` to `CochainComplex.mapBifunctorShift₁Iso` for `F'`, modulo the commutation of
`Φ.mapHomologicalComplex` and of `Φ₁.mapHomologicalComplex` with the shift.

Neither `mapBifunctorShift₁Iso` carries a sign, so on the summand indexed by `(p, q)` the
statement is `ι_mapBifunctorTotalIso_hom` at `(p + x, q)`. -/
theorem mapBifunctorTotalIso_commShift₁ (x : ℤ) :
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mapBifunctorShift₁Iso K L F x).hom ≫
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso x).hom.app
          (CochainComplex.mapBifunctor K L F) ≫
        (CategoryTheory.shiftFunctor (CochainComplex D' ℤ) x).map
          (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) hε₁ hε₂ K L).hom =
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) hε₁ hε₂ (K⟦x⟧) L).hom ≫
        HomologicalComplex.mapBifunctorMap
          (((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso x).hom.app K)
          (𝟙 ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F'
          (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₁Iso
          ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F' x).hom := by
  refine (Iso.inv_comp_eq _).mp ?_
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [ι_mapBifunctorTotalIso_inv_assoc F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      hε₁ hε₂ (K⟦x⟧) L p q n hpq, HomologicalComplex.ι_mapBifunctorMap_assoc]
  dsimp only [Functor.mapHomologicalComplex_map_f, Functor.comp_obj]
  rw [← Functor.map_comp_assoc,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f K L F x p q n hpq (p + x) (n + x) rfl rfl,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f
      ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F' x p q n hpq
      (p + x) (n + x) rfl rfl]
  have key := ι_mapBifunctorTotalIso_hom F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hε₁ hε₂ K L (p + x) q (n + x)
    (by dsimp at hpq ⊢; lia)
  simp [key]

/-- **The transport of a total complex commutes with the shift in the second variable.**
`CategoryTheory.Functor.mapBifunctorTotalIso` carries `CochainComplex.mapBifunctorShift₂Iso` for
`F` to `CochainComplex.mapBifunctorShift₂Iso` for `F'`, modulo the commutation of
`Φ.mapHomologicalComplex` and of `Φ₂.mapHomologicalComplex` with the shift.

This is the half that carries the Koszul sign.  On the summand indexed by `(p, q)` both
`mapBifunctorShift₂Iso`s contribute the *same* unit `(p * y).negOnePow` — it is a function of the
index and the shift only — and it passes through `Φ.map` because `Φ` is additive, so what is
left is `ι_mapBifunctorTotalIso_hom` at `(p, q + y)`. -/
theorem mapBifunctorTotalIso_commShift₂ (y : ℤ) :
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mapBifunctorShift₂Iso K L F y).hom ≫
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso y).hom.app
          (CochainComplex.mapBifunctor K L F) ≫
        (CategoryTheory.shiftFunctor (CochainComplex D' ℤ) y).map
          (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) hε₁ hε₂ K L).hom =
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) hε₁ hε₂ K (L⟦y⟧)).hom ≫
        HomologicalComplex.mapBifunctorMap
          (𝟙 ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
          (((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso y).hom.app L) F'
          (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₂Iso
          ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F' y).hom := by
  refine (Iso.inv_comp_eq _).mp ?_
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [ι_mapBifunctorTotalIso_inv_assoc F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      hε₁ hε₂ K (L⟦y⟧) p q n hpq, HomologicalComplex.ι_mapBifunctorMap_assoc]
  dsimp only [Functor.mapHomologicalComplex_map_f, Functor.comp_obj]
  rw [← Functor.map_comp_assoc,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f K L F y p q n hpq (q + y) (n + y) rfl rfl,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
      ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F' y p q n hpq
      (q + y) (n + y) rfl rfl]
  have key := ι_mapBifunctorTotalIso_hom F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hε₁ hε₂ K L p (q + y) (n + y)
    (by dsimp at hpq ⊢; lia)
  simp [key]

end Legs

/-! ### The transport as a shift-compatible morphism of bifunctors

The two lemmas above are, on the nose, the two component conditions of
`CategoryTheory.NatTrans.CommShift₂`: the `CategoryTheory.Functor.CommShift` datum of the source
bifunctor evaluated at a complex is `CategoryTheory.CommShift.comp` of
`CochainComplex.mapBifunctorShift₂Iso` with the commutation of `Φ.mapHomologicalComplex`, and
that of the target is `CommShift.comp` of the commutation of `Φ₂.mapHomologicalComplex` with
`mapBifunctorShift₂Iso` for `F'` — which is what the two sides of
`mapBifunctorTotalIso_commShift₂` spell out.  So this section only has to say so.
-/

section Bifunctor

/-- `mapBifunctorTotalIso_commShift₁` with the two commutation isomorphisms packaged as those of
the composite functors they are the `CategoryTheory.CommShift.comp` data of.  This is the
`CategoryTheory.NatTrans.CommShift` condition for the first variable verbatim. -/
theorem commShiftIso_hom_app_comp_mapBifunctorTotalIso₁
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) (x : ℤ) :
    ((F.map₂CochainComplex.flip.obj L ⋙
            Φ.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso x).hom.app K ≫
        (CategoryTheory.shiftFunctor (CochainComplex D' ℤ) x).map
          (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) hε₁ hε₂ K L).hom =
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) hε₁ hε₂ (K⟦x⟧) L).hom ≫
        ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          F'.map₂CochainComplex.flip.obj
            ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).commShiftIso x).hom.app K := by
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app, Category.assoc]
  exact mapBifunctorTotalIso_commShift₁ F F' Φ₁ Φ₂ Φ ε hε₁ hε₂ K L x

/-- `mapBifunctorTotalIso_commShift₂` in the same packaging: the
`CategoryTheory.NatTrans.CommShift` condition for the second variable verbatim. -/
theorem commShiftIso_hom_app_comp_mapBifunctorTotalIso₂
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) (y : ℤ) :
    ((F.map₂CochainComplex.obj K ⋙
            Φ.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso y).hom.app L ≫
        (CategoryTheory.shiftFunctor (CochainComplex D' ℤ) y).map
          (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) hε₁ hε₂ K L).hom =
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) hε₁ hε₂ K (L⟦y⟧)).hom ≫
        ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          F'.map₂CochainComplex.obj
            ((Φ₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).commShiftIso y).hom.app L := by
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app, Category.assoc]
  exact mapBifunctorTotalIso_commShift₂ F F' Φ₁ Φ₂ Φ ε hε₁ hε₂ K L y

/-- **The transport of a total complex, as an isomorphism of bifunctors on cochain complexes.**
This is the curried form of
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPairTransport`, at the spelling the shift
closure properties of `CategoryTheory.Functor.CommShift₂` match: the source is
`CategoryTheory.Functor.map₂CochainComplex` postcomposed with `Φ.mapHomologicalComplex` and the
target is `F'.map₂CochainComplex` precomposed with `Φ₁.mapHomologicalComplex` and
`Φ₂.mapHomologicalComplex`. -/
noncomputable def mapBifunctorTotalBifunctorIso :
    F.map₂CochainComplex ⋙ (Functor.whiskeringRight _ _ _).obj
          (Φ.mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      Φ₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ (F'.map₂CochainComplex ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Φ₂.mapHomologicalComplex (ComplexShape.up ℤ))) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun L => mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) hε₁ hε₂ K L)
      (fun {L L'} v => by
        have h := mapBifunctorTotalIso_hom_naturality F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hε₁ hε₂ K K L L' (𝟙 K) v
        rw [Functor.map_id] at h
        exact h))
    (fun {K K'} u => NatTrans.ext (funext fun L => by
      have h := mapBifunctorTotalIso_hom_naturality F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hε₁ hε₂ K K' L L u (𝟙 L)
      rw [Functor.map_id] at h
      exact h))

/-- **The transport of a total complex is compatible with the shifts in both variables.**
`CategoryTheory.NatTrans.CommShift₂` is exactly the pair of conditions
`mapBifunctorTotalIso_commShift₂` (for the second variable, at each fixed complex in the first)
and `mapBifunctorTotalIso_commShift₁` (for the first), once the `Functor.CommShift` data of the
source and target bifunctors are unfolded with
`CategoryTheory.Functor.commShiftIso_comp_hom_app`.

This is the shape in which the third leg of
`Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂` is consumed. -/
instance mapBifunctorTotalBifunctorIso_commShift₂ :
    NatTrans.CommShift₂Int
      (mapBifunctorTotalBifunctorIso F F' Φ₁ Φ₂ Φ ε hε₁ hε₂).hom where
  commShift_app K := ⟨fun y => NatTrans.ext (funext fun L =>
    commShiftIso_hom_app_comp_mapBifunctorTotalIso₂ F F' Φ₁ Φ₂ Φ ε hε₁ hε₂ K L y)⟩
  commShift_flipApp L := ⟨fun x => NatTrans.ext (funext fun K =>
    commShiftIso_hom_app_comp_mapBifunctorTotalIso₁ F F' Φ₁ Φ₂ Φ ε hε₁ hε₂ K L x)⟩

/-- **The components of `mapBifunctorTotalBifunctorIso` are the comparisons
`CategoryTheory.Functor.mapBifunctorTotalIso` it is assembled from.**

It holds by `rfl`, and stating it is nevertheless what makes it usable.  A consumer has the same
comparisons packaged as a transformation on the *product* category —
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPairTransport`, a
`CategoryTheory.NatIso.ofComponents` over the very same family — and so has to identify the two
packagings.  At the concrete bifunctor that identification is a kernel timeout if it is asked for
as one `rfl` on the whole transformation; read off the components by name, here, where every
category and functor is a variable, and it is free. -/
theorem mapBifunctorTotalBifunctorIso_hom_app_app
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    ((mapBifunctorTotalBifunctorIso F F' Φ₁ Φ₂ Φ ε hε₁ hε₂).hom.app K).app L =
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) hε₁ hε₂ K L).hom :=
  rfl

/-- The companion of `mapBifunctorTotalBifunctorIso_hom_app_app` for the inverse — the direction
in which the comparison of total complexes occurs in the second comparison of
[Stacks, Tag 079U]. -/
theorem mapBifunctorTotalBifunctorIso_inv_app_app
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    ((mapBifunctorTotalBifunctorIso F F' Φ₁ Φ₂ Φ ε hε₁ hε₂).inv.app K).app L =
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) hε₁ hε₂ K L).inv :=
  rfl

end Bifunctor

end CategoryTheory.Functor

end
