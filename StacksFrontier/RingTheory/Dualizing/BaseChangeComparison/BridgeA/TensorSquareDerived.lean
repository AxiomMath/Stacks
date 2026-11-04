module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareComplex

/-!
# The projection formula at the two ring maps of a pushout square, derived

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareComplex` pairs the two
instances of the projection formula attached to a pushout square

```
S --g--> T
|        |
p        w
v        v
S' --h-> T'
```

of commutative rings on **cochain complexes**.  Its implementation notes record what is still owed
before the pairing reaches `Dualizing.derivedExtendRestrictScalarsTensorIso`, the factor of the
keystone `Dualizing.TensorComparisonCompatibility` that
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail` reads at two different ring maps: the
derived pairing at equal universes, and the transport of that across the universe lift.  This file
discharges the derived pairing.

The equation is between two morphisms of `D(S')`.  Its left-hand side is the base change along `p`
of the component of `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse` at `g`, read at
the class of a K-flat complex `K`; its right-hand side runs through the component at `h`, read at
the class of `S' ⊗_S K`, which is K-flat by Stacks 06Y1.  Each component is evaluated by
`Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app`: the comparison morphism of
the derived extension of scalars, the identification of derived restriction of scalars with
termwise restriction, the chain-level projection formula, and the tensor comparison of the K-flat
model.  The two chain-level projection formulas are exactly what the pairing
`Dualizing.extendRestrictScalarsComplexIso_square` relates; the surrounding factors are carried
across by naturality of the comparison morphism of derived extension of scalars along `p`, which is
the only property of that model used here — no universal property of it is needed.

One of the four comparisons of the square is identified here with its derived counterpart: the
pushout comparison `MilnorPatching.pushoutBaseChange` is, on the nose, the underived comparison of
Stacks 065Z that `RingTheory.TorIndependence.derivedBaseChangeComparison` lifts, and that
comparison is what
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` computes the keystone's own square
comparison in terms of.

**What is not done here.**  `Dualizing.TensorComparisonCompatibility` is not proved and no tag
loses its conditional caveat.  The two remaining comparisons of the square — the identification of
the two extensions of scalars along the diagonal, and the lifted algebra — and the monoidality of
extension of scalars are read here at chain level, through `DerivedCategory.Q`, rather than as the
derived comparisons the keystone is stated with.  The identifications that remain are listed in
the implementation notes, each with the equation that evaluates the derived comparison at a class.

## Main results

* `Stacks.CategoryTheory.comp_cancel_last` — a trailing retraction cancels, over a variable
  category, which is how the component equation of the equal-universe projection formula is read
  with its tensor comparison moved across.
* `Stacks.CategoryTheory.inv_comp_two` — two retractions compose to a retraction of the composite.
* `Stacks.CategoryTheory.comp_eq_of_chain_pairing` — **the shape of the argument**, over variable
  categories: a chain-level equation between a map and a five-factor composite, together with the
  values of two derived components and one naturality square, gives the derived equation.
* `Dualizing.pushoutBaseChange_inv_eq_derivedBaseChangeComparison` — the pushout comparison of the
  square is the underived comparison of Stacks 065Z, which is the form the keystone's own square
  comparison is computed in.
* `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_square` — **the derived pairing at
  equal universes**, at the class of a K-flat complex.

## Implementation notes

The argument is run through `Stacks.CategoryTheory.comp_eq_of_chain_pairing`, whose morphisms are
all variables, for the reason recorded on
`Stacks.CategoryTheory.eq_of_glued_factorizations`: the source of the pushout comparison is
`Ext_p (Res_g (Ext_g K))` while the target of the base-changed projection formula is
`Ext_p ((Ext_g ⋙ Res_g) K)`, and the two are definitionally but not syntactically equal, so a
tactic that rebuilds the goal in place rejects the composite as ill-typed.  Instantiating a
statement over variable morphisms with `exact` crosses each such gap once, at default
transparency.

The comparison morphism of the derived extension of scalars along `h` is taken as an isomorphism
`eH` together with the equation identifying it with that morphism, rather than through `IsIso`:
the inverse is needed in the statement itself, and a caller supplies `eH` from
`CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat` at the K-flat
complex `S' ⊗_S K`.  The K-flatness of that complex is likewise an argument, since it occurs in
the statement as the hypothesis of a tensor comparison; Stacks 06Y1,
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`, supplies it.

**The identifications still owed.**  Reading the derived pairing with the derived comparisons of
the keystone in place of `DerivedCategory.Q` of the chain-level ones needs, one for each remaining
factor:

* the identification of the two extensions of scalars along the diagonal against
  `Dualizing.derivedBaseChangeSquareIso`, evaluated by
  `Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj`;
* the lifted algebra against `Dualizing.derivedBaseChangeAlgebraIso`, evaluated by
  `Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single`;
* the monoidality isomorphism `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` against the
  [stacks 068I] morphism `Dualizing.tensorBaseChangeMor`, evaluated by
  `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
open StacksDraft.DerivedHom

universe u

namespace Stacks.CategoryTheory

/-- **A trailing retraction cancels.**  A morphism `x` equal to `a ≫ b ≫ c ≫ d`, read against a
retraction `d'` of `d`, is `a ≫ b ≫ c`.

Stated over a variable category: the instantiation is at a composite of derived categories whose
intermediate objects carry two definitionally but not syntactically equal spellings, and a tactic
that rebuilds such a goal in place rejects it. -/
theorem comp_cancel_last {C : Type*} [Category* C] {P R₁ R₂ R₃ W : C}
    (x : P ⟶ W) (a : P ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃)
    (d : R₃ ⟶ W) (d' : W ⟶ R₃) (hx : x = a ≫ b ≫ c ≫ d) (hd : d ≫ d' = 𝟙 R₃) :
    x ≫ d' = a ≫ b ≫ c := by
  simp [hx, hd]

/-- **Two retractions compose to a retraction of the composite.**  If `a'` is a retraction of `a`
and `b'` of `b`, then `b' ≫ a'` is one of `a ≫ b`.

Recorded as the equation rather than through `IsIso`, in the manner of
`Stacks.CategoryTheory.comp_cancel_two`: an `IsIso` hypothesis carries the object spellings in its
indices, where instance resolution does not cross between two definitionally equal ones. -/
theorem inv_comp_two {C : Type*} [Category* C] {R₁ R₂ R₃ : C}
    (a : R₁ ⟶ R₂) (a' : R₂ ⟶ R₁) (b : R₂ ⟶ R₃) (b' : R₃ ⟶ R₂)
    (ha : a' ≫ a = 𝟙 R₂) (hb : b' ≫ b = 𝟙 R₃) : (b' ≫ a') ≫ a ≫ b = 𝟙 R₃ := by
  simp [reassoc_of% ha, hb]

/-- **A chain-level pairing becomes a derived one.**  Let `Q`, `Q'` be functors out of two
categories `Ch`, `Ch'` of chain-level objects, `Ep : Ch ⥤ Ch'` a chain-level base change, `Bp` a
derived one and `βp : Q ⋙ Bp ⟶ Ep ⋙ Q'` the comparison between them.  Suppose

* a chain-level morphism `u` has `Ep.map u` equal to a five-factor composite whose middle factor
  is a chain-level morphism `u'`;
* a derived morphism `pg`, read against `tg`, is `qg₁ ≫ qg₂ ≫ Q.map u`; and
* a derived morphism `ph`, read against `th`, is `qh ≫ Q'.map u'`, with `qh'` a retraction
  of `qh`.

Then the base change along `Bp` of `pg`, read against `tg` and `βp`, is the composite in which
`ph` replaces `u'`.  Nothing is assumed invertible beyond the one retraction, nothing of the four
categories, and `βp` is used only through its naturality square at `u`.

Every morphism is a variable, so that at the instantiation each gap between two definitionally but
not syntactically equal spellings is crossed once, by `exact`, at default transparency; see the
implementation notes of this file. -/
theorem comp_eq_of_chain_pairing {Ch C Ch' D : Type*}
    [Category* Ch] [Category* C] [Category* Ch'] [Category* D]
    (Q : Ch ⥤ C) (Q' : Ch' ⥤ D) (Ep : Ch ⥤ Ch') (Bp : C ⥤ D)
    (βp : Q ⋙ Bp ⟶ Ep ⋙ Q')
    {a b : Ch} (u : a ⟶ b)
    {a' b' x₁ x₂ : Ch'} (u' : a' ⟶ b')
    (c₁ : Ep.obj a ⟶ x₁) (c₂ : x₁ ⟶ a') (c₃ : b' ⟶ x₂) (c₄ : x₂ ⟶ Ep.obj b)
    (hchain : Ep.map u = c₁ ≫ c₂ ≫ u' ≫ c₃ ≫ c₄)
    {Z Y W : C} (pg : Z ⟶ W) (tg : W ⟶ Q.obj b) (qg₁ : Z ⟶ Y) (qg₂ : Y ⟶ Q.obj a)
    (hg : pg ≫ tg = qg₁ ≫ qg₂ ≫ Q.map u)
    {Z' W' : D} (ph : Z' ⟶ W') (th : W' ⟶ Q'.obj b')
    (qh : Z' ⟶ Q'.obj a') (qh' : Q'.obj a' ⟶ Z') (hqh : qh' ≫ qh = 𝟙 (Q'.obj a'))
    (hh : qh ≫ Q'.map u' = ph ≫ th) :
    Bp.map pg ≫ Bp.map tg ≫ βp.app b =
      Bp.map qg₁ ≫ Bp.map qg₂ ≫ βp.app a ≫ Q'.map c₁ ≫ Q'.map c₂ ≫
        qh' ≫ ph ≫ th ≫ Q'.map c₃ ≫ Q'.map c₄ := by
  have hu' : Q'.map u' = qh' ≫ ph ≫ th := by
    rw [← hh, ← Category.assoc, hqh, Category.id_comp]
  have hnat : Bp.map (Q.map u) ≫ βp.app b = βp.app a ≫ Q'.map (Ep.map u) := βp.naturality u
  calc Bp.map pg ≫ Bp.map tg ≫ βp.app b
      = Bp.map (pg ≫ tg) ≫ βp.app b := by rw [Bp.map_comp, Category.assoc]
    _ = Bp.map (qg₁ ≫ qg₂ ≫ Q.map u) ≫ βp.app b := by rw [hg]
    _ = Bp.map qg₁ ≫ Bp.map qg₂ ≫ Bp.map (Q.map u) ≫ βp.app b := by
        simp only [Bp.map_comp, Category.assoc]
    _ = Bp.map qg₁ ≫ Bp.map qg₂ ≫ βp.app a ≫ Q'.map (Ep.map u) := by rw [hnat]
    _ = Bp.map qg₁ ≫ Bp.map qg₂ ≫ βp.app a ≫
          Q'.map (c₁ ≫ c₂ ≫ u' ≫ c₃ ≫ c₄) := by rw [hchain]
    _ = _ := by simp only [Q'.map_comp, hu', Category.assoc]

end Stacks.CategoryTheory

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']

/-- **The pushout comparison of the square is the underived comparison of Stacks 065Z.**  For a
pushout square `w ∘ g = h ∘ p`, the inverse of `MilnorPatching.pushoutBaseChange` — restricting
along `h` the extension along `w`, read as the extension along `p` of the restriction along `g` —
is the underived comparison that
`RingTheory.TorIndependence.derivedBaseChangeComparison` lifts to derived categories.  Both carry
the pure tensor `s ⊗ m` to `h s ⊗ m`, and extension of scalars is generated by pure tensors with
first factor `1`, so the two agree.

This is what makes the chain-level pushout comparison of
`Dualizing.pushoutBaseChangeComplex` comparable with the derived comparison
`Dualizing.restrictionBaseChangeIsoGeneral`, whose inverse at a class is computed by
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` in terms of exactly this underived
transformation.  The two models of derived extension of scalars along the left and right edges
occur only as arguments of the comparison; no property of them is used. -/
theorem pushoutBaseChange_inv_eq_derivedBaseChangeComparison
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (Bp : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} S'))
    (Bw : DerivedCategory (ModuleCat.{u} T) ⥤ DerivedCategory (ModuleCat.{u} T'))
    (βp : DerivedCategory.Q ⋙ Bp ⟶
      (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (βw : DerivedCategory.Q ⋙ Bw ⟶
      (ModuleCat.extendScalars.{u, u, u} w).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [Bp.IsLeftDerivedFunctor βp
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))]
    [Bw.IsLeftDerivedFunctor βw
      (HomologicalComplex.quasiIso (ModuleCat.{u} T) (ComplexShape.up ℤ))] :
    (MilnorPatching.pushoutBaseChange g p w h comm hp).inv =
      (RingTheory.TorIndependence.derivedBaseChangeComparison
        g p w h comm Bp Bw βp βw).1 := by
  have hap : (ModuleCat.extendScalars.{u, u, u} p).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} p).isLeftAdjoint
  have haw : (ModuleCat.extendScalars.{u, u, u} w).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} w).isLeftAdjoint
  refine NatTrans.ext (funext fun M => ModuleCat.ExtendScalars.hom_ext (fun m => ?_))
  exact Eq.trans (MilnorPatching.pushoutBaseChangeIso_inv_tmul g p w h comm hp M 1 m)
    (RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_tmul
      g p w h comm Bp Bw βp βw M 1 m).symm

/-- **The projection formula at the two ring maps of a pushout square, derived at equal
universes.**  For a pushout square `w ∘ g = h ∘ p` of commutative rings in one universe, arbitrary
models `G`, `H` of derived extension of scalars along `g` and `h`, and an arbitrary model `Bp` of
derived extension of scalars along `p` with comparison morphism `βp`: the base change along `p` of
the component of `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse` at `g`, read at
the class of a K-flat complex `K` and against the tensor comparison of the K-flat model, is the
same formula at `h`, read at the class of `S' ⊗_S K`, conjugated by the three comparisons of the
square and the monoidality of extension of scalars.

This is the derived step owed by the implementation notes of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareComplex`, with the
three square comparisons and the monoidality isomorphism read at chain level through
`DerivedCategory.Q`; the four identifications that replace them by the derived comparisons the
keystone `Dualizing.TensorComparisonCompatibility` is stated with are listed in this file's
implementation notes.

Only the naturality of `βp` is used, so `Bp` carries no universal property; the two models `G` and
`H` are total left derived functors, which is what makes their component equations available. -/
theorem derivedExtendRestrictScalarsTensorIsoEqualUniverse_square
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (G : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} T))
    (βG : DerivedCategory.Q ⋙ G ⟶ CochainComplex.extendScalarsLarge g ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor βG
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))]
    (H : DerivedCategory (ModuleCat.{u} S') ⥤ DerivedCategory (ModuleCat.{u} T'))
    (βH : DerivedCategory.Q ⋙ H ⟶ CochainComplex.extendScalarsLarge h ⋙ DerivedCategory.Q)
    [H.IsLeftDerivedFunctor βH
      (HomologicalComplex.quasiIso (ModuleCat.{u} S') (ComplexShape.up ℤ))]
    (Bp : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} S'))
    (βp : DerivedCategory.Q ⋙ Bp ⟶
      (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (hK : K.KFlat)
    (hKp : CochainComplex.KFlat
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (eH : H.obj (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≅
        DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge h).obj
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (heH : eH.hom = βH.app
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    Bp.map ((derivedExtendRestrictScalarsTensorIsoEqualUniverse g G βG).hom.app
            (DerivedCategory.Q.obj K)) ≫
        Bp.map (((DerivedInternalHom.Model.adjunction S).tensorIso
            ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
              ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) K hK).hom) ≫
          βp.app ((MonoidalCategory.tensorLeft
            ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
              ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T)))).obj K) =
      Bp.map ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map (βG.app K)) ≫
        Bp.map (((ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.app
            ((CochainComplex.extendScalarsLarge g).obj K)).hom) ≫
          βp.app ((CochainComplex.extendScalarsLarge g ⋙
            CochainComplex.restrictScalarsLarge g).obj K) ≫
            DerivedCategory.Q.map ((pushoutBaseChangeComplex g p w h comm hp).inv.app
              (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) ≫
            DerivedCategory.Q.map
              (((ModuleCat.restrictScalars.{u} h).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
                ((extendScalarsSquareIsoComplex g p w h comm).inv.app K)) ≫
            (((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.app
                ((CochainComplex.extendScalarsLarge h).obj
                  (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K))).inv ≫
              (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map eH.inv) ≫
            (derivedExtendRestrictScalarsTensorIsoEqualUniverse h H βH).hom.app
              (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K)) ≫
            ((DerivedInternalHom.Model.adjunction S').tensorIso
              ((CochainComplex.singleFunctor (ModuleCat.{u} S') 0).obj
                ((ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of T' T')))
              (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) hKp).hom ≫
            DerivedCategory.Q.map ((pushoutAlgebraIsoComplex g p w h comm hp).inv ▷
              (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) ≫
            DerivedCategory.Q.map
              (CochainComplex.ExtendScalars.extendScalarsMonoidalIso p
                ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
                  ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) K).hom := by
  have hh : ((ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map eH.hom ≫
          ((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.app
            ((CochainComplex.extendScalarsLarge h).obj
              (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).hom) ≫
        DerivedCategory.Q.map ((extendRestrictScalarsComplexIso h).hom.app
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) =
      (derivedExtendRestrictScalarsTensorIsoEqualUniverse h H βH).hom.app
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) ≫
        ((DerivedInternalHom.Model.adjunction S').tensorIso
          ((CochainComplex.singleFunctor (ModuleCat.{u} S') 0).obj
            ((ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of T' T')))
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) hKp).hom := by
    rw [heH, Category.assoc]
    exact (Stacks.CategoryTheory.comp_cancel_last _ _ _ _ _ _
      (derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app h H βH _ hKp)
      (Iso.inv_hom_id _)).symm
  exact Stacks.CategoryTheory.comp_eq_of_chain_pairing DerivedCategory.Q DerivedCategory.Q
    ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)) Bp βp
    ((extendRestrictScalarsComplexIso g).hom.app K)
    ((extendRestrictScalarsComplexIso h).hom.app
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))
    _ _ _ _ (extendRestrictScalarsComplexIso_square g p w h comm hp K)
    _ _ _ _
    (Stacks.CategoryTheory.comp_cancel_last _ _ _ _ _ _
      (derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app g G βG K hK)
      (Iso.inv_hom_id _))
    _ _ _
    (((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.app
        ((CochainComplex.extendScalarsLarge h).obj
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K))).inv ≫
      (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map eH.inv)
    (Stacks.CategoryTheory.inv_comp_two _ _ _ _
      (by rw [← Functor.map_comp, eH.inv_hom_id, CategoryTheory.Functor.map_id]; rfl)
      (Iso.inv_hom_id _))
    hh

end Dualizing

end
