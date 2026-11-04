module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.MapHomotopyCategoryMate
public import StacksFrontier.CategoryTheory.Functor.Derived.ComparisonSquareChase

/-!
# A three-factor identification of functors on homotopy categories

An identification `g^* ⋙ f^* ≅ k^*` of functors induced on homotopy categories by a factorisation
`f ≫ g = k` is built in three factors: the comparison
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` of the induced functors, an isomorphism
induced by an isomorphism of the target functors, and the renaming along the factorisation.  This
file shows that the three contract to a single `mapHomotopyCategoryCompIso`, of the corresponding
contraction of the degreewise functors.

That contraction is what lets a chase on homotopy categories be reduced to a chase on complexes:
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` is, at the image of a complex, the image of
the degreewise comparison, while a three-factor composite is not.

Everything here is stated for arbitrary categories and functors.  At the concrete data of an
identification of pullbacks along morphisms of small étale ringed topoi the composite of the
degreewise functors appears in the type of a `CategoryTheory.NatIso.mapHomologicalComplex`, and
elaborating that type costs a sizeable fraction of the heartbeat budget; recording the contraction
as an equation of isomorphisms, where no such type occurs, keeps it out of this step.

## Main results

* `StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_trans_eqToIso`: the comparison of the
  induced functors followed by a renaming along an equality of indices is the comparison of the
  degreewise contraction followed by the degreewise renaming.
* `StacksDraft.ComparisonSquare.factorIso_three_eq`: the three-factor identification is the
  comparison of a single degreewise contraction.
* `StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient'`: the comparison on
  homotopy categories is, at the image of a complex, the image of the comparison on complexes.
* `StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_hom_app_f`,
  `StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_inv_app_f` and
  `StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_refl_inv_app_f`: the comparison on
  complexes, and the one at an identity read backwards, in a single degree.
* `StacksDraft.ComparisonSquare.comp_four_hom_ext`: a composite of four morphisms of complexes,
  checked in each degree.
* `StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle`: a cocycle of natural
  transformations whose leading factor is a contraction of two functors passes to complexes.

## Why `CategoryTheory.Functor.mapHomologicalComplexCompIso`

The declarations about complexes are stated with
`CategoryTheory.Functor.mapHomologicalComplexCompIso`, not with the
`CategoryTheory.NatIso.mapHomologicalComplex` it is defined to be.  The two are the same term with
different ascribed types — `F^• ⋙ G^• ≅ H^•` against `(F ⋙ G)^• ≅ H^•` — so the conversion
identifying `(F ⋙ G)^•` with `F^• ⋙ G^•` is performed once, in Mathlib, where the functors are
variables.  Written at concrete functors that conversion unfolds the construction of an inverse
image of sheaves of modules and costs more than the whole heartbeat budget; with the ascribed
spelling it never arises.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksDraft.ComparisonSquare

variable {V W W' : Type*} [Category* V] [Category* W] [Category* W'] [Preadditive V]
  [Preadditive W] [Preadditive W'] {ι : Type*}

/-- **The comparison of the induced functors, followed by a renaming along an equality of
indices.**  It is the comparison of the degreewise contraction followed by the degreewise
renaming.

The equality of indices is a hypothesis rather than a `rfl`, which is what makes the statement
provable: the two renamings are `CategoryTheory.eqToIso` of the image of that equality under two
different families of functors, and substituting it is the only way to see that they agree. -/
theorem mapHomotopyCategoryCompIso_trans_eqToIso (P : ι → (V ⥤ W')) [∀ i, (P i).Additive]
    (c : ComplexShape ℤ) {F : V ⥤ W} {G : W ⥤ W'} [F.Additive] [G.Additive] {i j : ι}
    (e : F ⋙ G ≅ P i) (hij : i = j) :
    Functor.mapHomotopyCategoryCompIso e c ≪≫
        eqToIso (congrArg (fun k => (P k).mapHomotopyCategory c) hij) =
      Functor.mapHomotopyCategoryCompIso (e ≪≫ eqToIso (congrArg P hij)) c := by
  subst hij
  rw [show eqToIso (congrArg (fun k => (P k).mapHomotopyCategory c) (rfl : i = i)) =
      Iso.refl ((P i).mapHomotopyCategory c) from rfl, Iso.trans_refl,
    show eqToIso (congrArg P (rfl : i = i)) = Iso.refl (P i) from rfl, Iso.trans_refl]

/-- **A three-factor identification of functors on homotopy categories is a single comparison.**
The comparison of the induced functors for `e`, the isomorphism induced by `τ`, and the renaming
along `hij` compose to the comparison of the induced functors for the degreewise contraction
`κ ≪≫ eqToIso (congrArg P hij)`.

The contraction `κ` of the two degreewise functors is a separate argument, pinned by `hκ`, so that
the conclusion can be stated at the spelling a consumer holds it at rather than at `e ≪≫ τ`; the
two differ in the bracketing of the composite, which is not an identity in a general category. -/
theorem factorIso_three_eq (P : ι → (V ⥤ W')) [∀ i, (P i).Additive] (c : ComplexShape ℤ)
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) {i j : ι} (τ : H ≅ P i) (κ : F ⋙ G ≅ P i) (hκ : e ≪≫ τ = κ) (hij : i = j) :
    Functor.mapHomotopyCategoryCompIso e c ≪≫ Stacks.Homology.mapHomotopyCategoryIso τ c ≪≫
        eqToIso (congrArg (fun k => (P k).mapHomotopyCategory c) hij) =
      Functor.mapHomotopyCategoryCompIso (κ ≪≫ eqToIso (congrArg P hij)) c := by
  subst hκ
  rw [← Iso.trans_assoc, Functor.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso]
  exact mapHomotopyCategoryCompIso_trans_eqToIso P c (e ≪≫ τ) hij

/-- **The comparison of the induced functors on homotopy categories is, at the image of a complex,
the image of the comparison on complexes.**  The comparison on homotopy categories is lifted
through the quotient from the one on complexes, so this holds by construction.

This is `StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient` with the
comparison on complexes read at the ascribed spelling of
`CategoryTheory.Functor.mapHomologicalComplexCompIso`; see the note above on why that matters. -/
theorem mapHomotopyCategoryCompIso_inv_app_quotient' {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (c : ComplexShape ℤ)
    (N : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c).inv.app ((HomotopyCategory.quotient V c).obj N) =
      (HomotopyCategory.quotient W' c).map
        ((Functor.mapHomologicalComplexCompIso e c).inv.app N) :=
  rfl

end StacksDraft.ComparisonSquare

namespace StacksDraft.ComparisonSquare

variable {ι : Type*} {A A' Bc Bc' D D' : Type*} [Category* A] [Category* A'] [Category* Bc]
  [Category* Bc'] [Category* D] [Category* D'] [Preadditive A] [Preadditive A'] [Preadditive Bc]
  [Preadditive Bc'] [Preadditive D] [Preadditive D']
  {tR : A ⥤ A'} {tS : Bc ⥤ Bc'} {tT : D ⥤ D'} {pf : A' ⥤ Bc'} {pg : Bc' ⥤ D'} {pk : A' ⥤ D'}
  {ef : A ⥤ Bc} {eg : Bc ⥤ D} {ek : A ⥤ D}
  [tR.Additive] [tS.Additive] [tT.Additive] [pf.Additive] [pg.Additive] [pk.Additive]
  [ef.Additive] [eg.Additive] [ek.Additive]

/-- **The comparison of the induced functors on complexes, in a single degree**: the component of
the comparison at that term of the complex. -/
theorem mapHomologicalComplexCompIso_hom_app_f {V W W' : Type*} [Category* V] [Category* W]
    [Category* W'] [Preadditive V] [Preadditive W] [Preadditive W'] {F : V ⥤ W} {G : W ⥤ W'}
    {H : V ⥤ W'} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (c : ComplexShape ℤ)
    (M : HomologicalComplex V c) (n : ℤ) :
    ((Functor.mapHomologicalComplexCompIso e c).hom.app M).f n = e.hom.app (M.X n) :=
  rfl

/-- **The comparison of the induced functors on complexes, read backwards, in a single degree.** -/
theorem mapHomologicalComplexCompIso_inv_app_f {V W W' : Type*} [Category* V] [Category* W]
    [Category* W'] [Preadditive V] [Preadditive W] [Preadditive W'] {F : V ⥤ W} {G : W ⥤ W'}
    {H : V ⥤ W'} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (c : ComplexShape ℤ)
    (M : HomologicalComplex V c) (n : ℤ) :
    ((Functor.mapHomologicalComplexCompIso e c).inv.app M).f n = e.inv.app (M.X n) :=
  rfl

/-- **The comparison of the induced functors on complexes at an identity, read backwards, is an
identity in every degree.**  This is the factor that reconciles `(F ⋙ G)^•` with `F^• ⋙ G^•`. -/
theorem mapHomologicalComplexCompIso_refl_inv_app_f {V W W' : Type*} [Category* V] [Category* W]
    [Category* W'] [Preadditive V] [Preadditive W] [Preadditive W'] {F : V ⥤ W} {G : W ⥤ W'}
    [F.Additive] [G.Additive] [(F ⋙ G).Additive] (c : ComplexShape ℤ)
    (M : HomologicalComplex V c) (n : ℤ) :
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).inv.app M).f n = 𝟙 _ :=
  rfl

/-- **A composite of four morphisms of complexes, checked in each degree.** -/
theorem comp_four_hom_ext {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} {K₁ K₂ K₃ K₄ K₅ : HomologicalComplex C c}
    (a : K₁ ⟶ K₂) (b : K₂ ⟶ K₃) (d : K₃ ⟶ K₄) (e : K₄ ⟶ K₅) (m : K₁ ⟶ K₅)
    (h : ∀ n, a.f n ≫ b.f n ≫ d.f n ≫ e.f n = m.f n) :
    a ≫ b ≫ d ≫ e = m :=
  HomologicalComplex.hom_ext _ _ fun n => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact h n

/-- **A cocycle of natural transformations whose leading factor is a contraction passes to
complexes.**  If the square `cU`, `τf`, `τg`, `ε`, `τk` commutes at every object, then it commutes
at every complex, degreewise.

Stated for arbitrary categories and natural transformations on purpose.  Checking it in each
degree needs the identification of the term of degree `n` of a degreewise image of a complex with
the image of the term of degree `n`; at concrete functors that identification holds by definition
but the conversion check, run against functors whose definitions unfold, costs more than the
kernel's whole budget.  With the functors kept as variables nothing can unfold and the check is
structural.

This differs from `StacksDraft.ComparisonSquare.mapHomologicalComplex_cocycle` only in the leading
factor, which is here the comparison of the induced functors of a contraction `pf ⋙ pg ≅ pk`
rather than the degreewise image of its inverse; see the note above on why that matters. -/
theorem mapHomologicalComplexCompIso_cocycle (c : ComplexShape ℤ) (cU : pf ⋙ pg ≅ pk)
    (τf : tR ⋙ pf ⟶ ef ⋙ tS) (τg : tS ⋙ pg ⟶ eg ⋙ tT) (ε : ef ⋙ eg ⟶ ek)
    (τk : tR ⋙ pk ⟶ ek ⋙ tT)
    (h : ∀ N : A, cU.inv.app (tR.obj N) ≫ pg.map (τf.app N) ≫ τg.app (ef.obj N) ≫
      tT.map (ε.app N) = τk.app N)
    (M : HomologicalComplex A c) :
    (Functor.mapHomologicalComplexCompIso cU c).inv.app ((tR.mapHomologicalComplex c).obj M) ≫
        (pg.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex τf c).app M) ≫
        (NatTrans.mapHomologicalComplex τg c).app ((ef.mapHomologicalComplex c).obj M) ≫
        (tT.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex ε c).app M) =
      (NatTrans.mapHomologicalComplex τk c).app M :=
  HomologicalComplex.hom_ext _ _ fun n => h (M.X n)

end StacksDraft.ComparisonSquare

end
