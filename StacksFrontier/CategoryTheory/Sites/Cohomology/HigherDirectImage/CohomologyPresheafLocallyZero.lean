module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false


/-!
# The cohomology presheaf of a sheaf of modules on a site is locally zero in positive degree

Over a ringed site `(C, O)`, every cohomology class of positive degree on an object `U` is
killed by restricting along a suitable covering of `U`.

Throughout, `C` is a site (a category with a Grothendieck topology `J`), the sheaf of rings is
`R : Sheaf J RingCat`, and `Mod(O) = SheafOfModules R` is the abelian category of sheaves of
`O`-modules on `C`.  It has enough injectives, so every object admits an injective resolution.

Cohomology over an object `U` is `Hⁿ(U, F) = Hⁿ(Γ(U, I^•)) = Rⁿ Γ(U, -)(F)` for an injective
resolution `0 → F → I^•`, independently of the resolution up to canonical isomorphism.  A
morphism `φ : U' ⟶ U` induces the restriction map `Hⁿ(U, F) → Hⁿ(U', F)`, and a covering of `U`
is a term `S : J.Cover U`, whose members `g : S.Arrow` have source `g.Y` and covering morphism
`g.f : g.Y ⟶ U`.

## Main results

* `locality_of_cohomology`: for `n > 0` and `ξ ∈ Hⁿ(U, F)` there is a covering `{Uᵢ → U}` with
  `ξ|_{Uᵢ} = 0` in `Hⁿ(Uᵢ, F)` for every `i`.
* `mapExtendIso` and `auxIso`: the comparison isomorphisms identifying the extension of a
  cochain complex along `ComplexShape.embeddingUpNat` with the original complex, used to move
  between `Ext`-theoretic and resolution-theoretic descriptions of cohomology.

## Implementation notes

* Cohomology is realized through Mathlib's `Sheaf.cohomologyPresheaf`, defined via `Ext` in the
  abelian category `Sheaf J AddCommGrpCat`: for `G : Sheaf J AddCommGrpCat`, the value
  `(G.cohomologyPresheaf n).obj (op V)` is `Hⁿ(V, G)`, and functoriality of
  `cohomologyPresheaf` supplies the restriction maps.  For a sheaf of `O`-modules `F` we pass to
  the underlying abelian sheaf `(SheafOfModules.toSheaf R).obj F`, whose cohomology agrees with
  that of `F` because the forgetful functor identifies the derived functors.
* The hypothesis `0 < n` is essential: `H⁰(U, F) = F(U)`, and a nonzero global section need not
  be killed by any covering.
* The site is taken small (`[SmallCategory C]`, the standard convention for sheaf cohomology),
  which makes the canonical `HasExt.{u} (Sheaf J AddCommGrpCat.{u})` instance available and
  `Sheaf J AddCommGrpCat` Grothendieck-abelian with enough injectives;
  `[HasSheafify J AddCommGrpCat]` is what makes sense of `cohomologyPresheaf`.

## References

* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

open CategoryTheory Opposite Limits

namespace Stacks.Cohomology.Locality

universe u v w uC vC uA

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat]

/-- **Definition 1.** The `n`-th cohomology `H^n(U, F)` of a sheaf of `O`-modules
`F` over an object `U`, realized as the value over `U` of the abelian-sheaf
cohomology presheaf of the underlying sheaf of abelian groups
`(SheafOfModules.toSheaf R).obj F`. This is `R^n Gamma(U, -)(F)`. -/
noncomputable def cohomology (R : Sheaf J RingCat) (F : SheafOfModules R)
    (n : ℕ) (U : C) : AddCommGrpCat :=
  (((SheafOfModules.toSheaf R).obj F).cohomologyPresheaf n).obj (op U)

/-- **Definition 2.** The restriction map `H^n(U, F) -> H^n(U', F)` on cohomology
induced by a morphism `φ : U' -> U`, given by the functoriality of the cohomology
presheaf. -/
noncomputable def restriction (R : Sheaf J RingCat) (F : SheafOfModules R)
    (n : ℕ) {U U' : C} (φ : U' ⟶ U) :
    cohomology R F n U ⟶ cohomology R F n U' :=
  (((SheafOfModules.toSheaf R).obj F).cohomologyPresheaf n).map φ.op

/-! ### Decomposition of the proof

The Mathlib realization of `H^n(U,F)` is the value over `U` of the abelian-sheaf
cohomology presheaf
`P_n := ((SheafOfModules.toSheaf R).obj F).cohomologyPresheaf n : Cᵒᵖ ⥤ AddCommGrpCat`,
and `restriction R F n φ` is, *definitionally*, the presheaf map `P_n.map φ.op`
(see `restriction_apply`, proved here by `rfl`).

So the theorem says exactly: for `n > 0`, every section `ξ` of `P_n` over `U` is
killed after restricting along some covering of `U`. That is precisely the
statement that **the cohomology presheaf is locally zero in positive degree**,
which is the mathematical content of Stacks 01FW. We isolate this as the generic
sub-lemma `cohomologyPresheaf_locally_zero` (stated for an arbitrary abelian sheaf
`G`, since it is a property of `cohomologyPresheaf` itself); `locality_of_cohomology` then
reduces to it together with the definitional bridge `restriction_apply`.

A remark on universes, and on why the kernel is not phrased via `J.sheafify`. One is
tempted to factor `cohomologyPresheaf_locally_zero` through "the sheafification of
`G.cohomologyPresheaf n` is a zero object" + a generic `Plus`-API glue lemma. But
`G.cohomologyPresheaf n` lands in `AddCommGrpCat.{w}` (the universe of the `HasExt.{w}`
instance), whereas the available `HasSheafify J AddCommGrpCat` and the
`J.sheafify` / `presheafToSheaf` API are about `AddCommGrpCat.{v}`. Sheafifying the
cohomology presheaf would require `HasSheafify`/`HasWeakSheafify` for `AddCommGrpCat.{w}`,
which is not available here.  The locally-zero statement is therefore proved directly, via
the `Ext` description together with the concrete-sheafification API at the level of the
*underlying* abelian groups, rather than through a `J.sheafify`-of-`cohomologyPresheaf`
detour. -/

/-- Definitional bridge: applying the cohomology restriction map `restriction R F n φ`
to a class `ξ` is the same as applying the presheaf map `P_n.map φ.op`, where
`P_n = ((SheafOfModules.toSheaf R).obj F).cohomologyPresheaf n`. True by `rfl`
because `restriction` and `cohomology` are *defined* via `cohomologyPresheaf`. -/
theorem restriction_apply (R : Sheaf J RingCat) (F : SheafOfModules R)
    (n : ℕ) {U U' : C} (φ : U' ⟶ U) (ξ : cohomology R F n U) :
    (restriction R F n φ) ξ
      = (((SheafOfModules.toSheaf R).obj F).cohomologyPresheaf n).map φ.op ξ :=
  rfl

/-! **Analytic kernel of 01FW (n > 0): the cohomology presheaf is locally zero.**

For an abelian sheaf `G`, `n > 0`, an object `U` and a section
`ξ : (G.cohomologyPresheaf n).obj (op U) = Hⁿ(U, G)`, there is a covering
`S : J.Cover U` such that the restriction `(G.cohomologyPresheaf n).map g.f.op ξ`
vanishes for every member `g : S.Arrow`.

This is a property of `cohomologyPresheaf` itself, hence stated generically for `G`;
the main theorem applies it to `G = (SheafOfModules.toSheaf R).obj F`.

The argument runs as follows.
Choose an injective resolution `0 → G → I⁰ → I¹ → ⋯` of `G` in the abelian category
`Sheaf J AddCommGrpCat` (enough injectives). By definition `Hⁿ(V, G)` is the `n`-th
cohomology of the global-sections complex `Γ(V, I^•) : I⁰(V) → I¹(V) → ⋯`, with
differentials `d`, and the restriction maps are induced by the sheaf restriction
maps `Iᵖ(V) → Iᵖ(V')`. So `ξ` is represented by a cocycle
`ξ̃ ∈ ker(d : Iⁿ(U) → Iⁿ⁺¹(U))`.

Since `0 → G → I^•` is a resolution and `n > 0`, the complex of *sheaves* `I^•` is
exact at `Iⁿ`, i.e. as subsheaves of `Iⁿ`:
  `ker(d : Iⁿ → Iⁿ⁺¹) = im(d : Iⁿ⁻¹ → Iⁿ)`.
The cocycle `ξ̃` is a section over `U` of the kernel sheaf `ker(d)`, hence by the
displayed equality a section over `U` of the image sheaf `im(d)`. The image sheaf is
the *sheafification* of the presheaf image `V ↦ d(Iⁿ⁻¹(V)) ⊆ Iⁿ(V)`; a section of a
sheafification is, by the local nature of sheafification (concrete-sheafification
API: `GrothendieckTopology.Plus.eq_mk_iff_exists` and friends), locally in the
presheaf image. Therefore there is a covering `{U_i → U}` (i.e. `S : J.Cover U`) and
sections `η_i ∈ Iⁿ⁻¹(U_i)` with
  `ξ̃|_{U_i} = d η_i`   for every member `g : S.Arrow` (with `U_i = g.Y`).
Thus over each `U_i` the cocycle `ξ̃|_{U_i}` is a coboundary, so its cohomology
class — which is exactly `(G.cohomologyPresheaf n).map g.f.op ξ`, the restriction of
`ξ` to `U_i` — vanishes in `Hⁿ(U_i, G)`. Hence `S` kills `ξ`. ∎

(Equivalent `Ext`-native phrasing, matching Mathlib's actual definition
`G.cohomologyPresheaf n = (V ↦ Extⁿ(L V, G))`, `L V` = free sheaf on `yoneda V`:
the presheaf `V ↦ Extⁿ(L V, G)` has zero sheafification for `n > 0`, because
positive-degree `Ext` out of the local generators `L V` vanishes locally; translate
"dies in the sheafification" into "restricts to 0 on a covering" via
`Plus.eq_mk_iff_exists`. This route avoids building injective resolutions by hand
but needs a local-vanishing-of-positive-Ext input.) -/

/-- **Enough injectives.** For a small site `C` with a Grothendieck topology `J` and
`[HasSheafify J AddCommGrpCat]`, the abelian category `Sheaf J AddCommGrpCat` of sheaves
of abelian groups is Grothendieck-abelian, hence has enough injectives. This is the
structural input (gated behind `[SmallCategory C]`) behind the injective-resolution proof of
`ext_generator_locally_zero`. -/
@[sga "4 I 7.13" "special case",
  sga "4 V 0.1.1" "special case",
  sga "4 V 0.2.1" "special case",
  sga "4 V 2.5.2" "special case",
  sga "4½ Arcata 1.6.3" "special case"]
instance enoughInjectives_sheaf : EnoughInjectives (Sheaf J AddCommGrpCat.{u}) :=
  (Sheaf.instIsGrothendieckAbelian J AddCommGrpCat.{u}).enoughInjectives

/-- The "free sheaf on the Yoneda presheaf" generator `L V`, exactly as Mathlib's
`Sheaf.cohomologyPresheaf` is built from it:
`L V = (presheafToSheaf J AddCommGrpCat).obj (free.obj (yoneda.obj V))`. By the
(reducible) definition of `cohomologyPresheaf`, `(G.cohomologyPresheaf n).obj (op V)`
is *definitionally* `Abelian.Ext (L V) G n`, and the presheaf map along `φ : V' ⟶ V`
is precomposition (in `Ext`) by `L φ`. -/
@[sga "7 VII 1.4" "special case"]
noncomputable abbrev freeYonedaSheaf (V : C) : Sheaf J AddCommGrpCat :=
  (presheafToSheaf J AddCommGrpCat).obj
    (((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free).obj
      (yoneda.obj V))

/-- The section-presheaf cochain complex of an injective resolution `I` of `G`: apply
the (underlying-presheaf) forgetful functor `sheafToPresheaf` to the cocomplex of `I`.
Its value at `op V` is the complex of sections `I^•(V)`, and its `n`-th `homology` is the
presheaf `V ↦ Hⁿ(I^•(V))` whose local vanishing (degree `n > 0`) is the kernel of 01FW. -/
noncomputable abbrev sectionComplex {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max u v})
    (I : InjectiveResolution G) : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex _).obj I.cocomplex

/-- The Hom-complex `Hom_{Sheaf}(L V, I^•)` of an injective resolution `I` of `G`: apply the
additive corepresentable functor `preadditiveCoyoneda.obj (op (L V)) = Hom(L V, -)` to the
cocomplex of `I`. Its `n`-th `homology` computes `Extⁿ(L V, G)` (Lemma A) and, by free-Yoneda
corepresentability, agrees with `Hⁿ(I^•(V))` (Lemma B+C). -/
noncomputable abbrev homComplex (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (V : C) : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) V))).mapHomologicalComplex _).obj
    I.cocomplex

/-- The `Ext`-class precomposition by `L g` along `g : Y ⟶ U` — exactly the restriction
operation that appears in the statement of `ext_generator_locally_zero`. -/
noncomputable abbrev extRestrict (G : Sheaf J AddCommGrpCat) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (ξ : Abelian.Ext (freeYonedaSheaf (J := J) U) G n) :
    Abelian.Ext (freeYonedaSheaf (J := J) Y) G n :=
  (Abelian.Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
    (((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free).map
      (yoneda.map g)))).comp ξ (zero_add n)

/-! **Lemma A — `Ext` via the injective resolution.** For an injective resolution `I` of `G`,
the `n`-th `Ext` group `Extⁿ(L V, G)` is computed by the `n`-th homology of the Hom-complex
`Hom(L V, I^•)`. This is the standard injective-resolution computation of `Ext`. It is assembled
below from four helper isomorphisms (`homComplexSingleIsoCoyoneda`, `auxIso`,
`mapExtendIso`, `mapExtendHomologyIso`) together with Mathlib's
`InjectiveResolution.extAddEquivCohomologyClass` and `CochainComplex.HomComplex.homologyAddEquiv`.
-/

/-- **Lemma A, helper 1.** For a single complex `(single X)` and a ℤ-indexed cochain complex `L`,
the Hom-complex `Hom(single X, L)` is isomorphic, as a cochain complex of abelian groups, to the
result of applying the additive corepresentable functor
`Hom(X, -) = preadditiveCoyoneda.obj (op X)` degreewise to `L`. Degreewise this is
`Cochain.fromSingleEquiv`, and the differentials agree (no sign) by `Cochain.δ_fromSingleMk`. -/
noncomputable def homComplexSingleIsoCoyoneda
    {C' : Type uC} [Category.{vC} C'] [Abelian C'] (X : C') (L : CochainComplex C' ℤ) :
    ((CochainComplex.singleFunctor C' 0).obj X).HomComplex L ≅
      ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := X) (K := L) (p := 0) (q := j) (n := j) (by ring)).toAddCommGrpIso)
    (by
      intro i j hij
      have hij' : i + 1 = j := hij
      ext (α : CochainComplex.HomComplex.Cochain _ _ _)
      obtain ⟨f, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective α i (by ring)
      simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
        Functor.mapHomologicalComplex_obj_d, AddEquiv.toAddCommGrpIso_hom,
        AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
      have hLHS : (AddCommGrpCat.Hom.hom ((preadditiveCoyoneda.obj (op X)).map (L.d i j)))
            ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0:ℤ)+i=i))
              (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+i=i)))
          = f ≫ L.d i j := by
        rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]; rfl
      have h1 : (AddCommGrpCat.Hom.hom ((((CochainComplex.singleFunctor C' 0).obj X).HomComplex
          L).d i j))
            (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+i=i))
          = CochainComplex.HomComplex.δ i j
              (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+i=i)) :=
        CochainComplex.HomComplex_d_hom_apply _ _ i j _
      have hRHS : (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0:ℤ)+j=j))
            ((AddCommGrpCat.Hom.hom ((((CochainComplex.singleFunctor C' 0).obj X).HomComplex L).d i
                j))
              (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+i=i)))
          = f ≫ L.d i j := by
        rw [h1, CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (show (0:ℤ)+i=i by ring) j j
            (by ring),
          CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      exact hLHS.trans hRHS.symm)

/-- **Lemma A, helper 2.** Degreewise comparison iso for `mapExtendIso`: applying an additive
functor
`F` to the `Option`-indexed object `extend.X X o` (the building block of
`HomologicalComplex.extend`)
commutes with `extend` (using that `F` preserves zero objects and `extend.XIso`). -/
noncomputable def auxIso
    {C' D : Type uC} [Category.{vC} C'] [Category.{vC} D] [Abelian C'] [Abelian D]
    (F : C' ⥤ D) [F.Additive] (X : CochainComplex C' ℕ) :
    (o : Option ℕ) →
      F.obj (HomologicalComplex.extend.X X o) ≅
        HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X) o
  | none => (F.map_isZero (HomologicalComplex.extend.isZero_X X rfl)).iso
      (HomologicalComplex.extend.isZero_X _ rfl)
  | some i => F.mapIso (HomologicalComplex.extend.XIso X (j := i) rfl) ≪≫
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X)
        (j := i) rfl).symm

/-- The differentials commute with the `auxIso` comparison maps. -/
lemma auxIso_comm
    {C' D : Type uC} [Category.{vC} C'] [Category.{vC} D] [Abelian C'] [Abelian D]
    (F : C' ⥤ D) [F.Additive] (X : CochainComplex C' ℕ) (oi oj : Option ℕ) :
    (auxIso F X oi).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X) oi oj
      = F.map (HomologicalComplex.extend.d X oi oj) ≫ (auxIso F X oj).hom := by
  rcases oi with _ | a
  · rw [HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl,
      HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl]; simp
  · rcases oj with _ | b
    · rw [HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl,
        HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl]; simp
    · rw [HomologicalComplex.extend.d_eq _ rfl rfl, HomologicalComplex.extend.d_eq _ rfl rfl]
      simp only [auxIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        Functor.mapHomologicalComplex_obj_d, F.map_comp]
      simp

/-- **Lemma A, helper 3.** An additive functor `F` commutes with `HomologicalComplex.extend` along
the
canonical embedding `ℕ ↪ ℤ`, as an isomorphism of ℤ-indexed cochain complexes. -/
noncomputable def mapExtendIso
    {C' D : Type uC} [Category.{vC} C'] [Category.{vC} D] [Abelian C'] [Abelian D]
    (F : C' ⥤ D) [F.Additive] (X : CochainComplex C' ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.extend X ComplexShape.embeddingUpNat)
      ≅ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i' => auxIso F X (ComplexShape.embeddingUpNat.r i'))
    (fun {i j} _ =>
      auxIso_comm F X (ComplexShape.embeddingUpNat.r i) (ComplexShape.embeddingUpNat.r j))

/-- **Lemma A, helper 4.** The `n`-th homology (`n : ℕ`, viewed in `ℤ`) of `F` applied to the
ℤ-extension of a ℕ-indexed cochain complex agrees with the `n`-th homology of `F` applied to the
original ℕ-indexed complex. Combines `mapExtendIso` with `HomologicalComplex.extendHomologyIso`. -/
noncomputable def mapExtendHomologyIso
    {C' D : Type uC} [Category.{vC} C'] [Category.{vC} D] [Abelian C'] [Abelian D]
    (F : C' ⥤ D) [F.Additive] (X : CochainComplex C' ℕ) (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.extend X ComplexShape.embeddingUpNat)).homology (n : ℤ)
      ≅ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X).homology n :=
  (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n:ℤ)).mapIso (mapExtendIso F X) ≪≫
    HomologicalComplex.extendHomologyIso
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X) ComplexShape.embeddingUpNat
      (j := n) (j' := (n:ℤ)) (by simp [ComplexShape.embeddingUpNat])

/-- **Lemma A — `Ext` via the injective resolution.** The chain is:
`Extⁿ(L V, G) ≃+ CohomologyClass (single (L V)) I.cochainComplex n` (Mathlib's
`InjectiveResolution.extAddEquivCohomologyClass`), `≃+ Hⁿ(Hom(single (L V), I.cochainComplex))`
(`CochainComplex.HomComplex.homologyAddEquiv`), `≅ Hⁿ(Hom(L V, -) applied to I.cochainComplex)`
(`homComplexSingleIsoCoyoneda`), `≅ Hⁿ(Hom(L V, I^•))` (`mapExtendHomologyIso`, using that
`I.cochainComplex` is the ℤ-extension of `I.cocomplex`). -/
noncomputable def extEquivHomComplexHomology (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) (V : C) :
    Abelian.Ext (freeYonedaSheaf (J := J) V) G n ≃+
      ((homComplex G I V).homology n) :=
  (I.extAddEquivCohomologyClass).trans <|
  ((CochainComplex.HomComplex.homologyAddEquiv
    ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj (freeYonedaSheaf (J := J) V))
    I.cochainComplex (↑n)).symm).trans <|
  (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
    (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) V)
      I.cochainComplex)).addCommGroupIsoToAddEquiv).trans <|
  (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) V)))
    I.cocomplex n).addCommGroupIsoToAddEquiv

/-- **Lemma B+C, helper.** For an additive adjunction `F ⊣ Gf` between preadditive categories,
the corepresentable functor `Hom(F.obj X, -)` is naturally isomorphic to `Gf ⋙ Hom(X, -)`. This
is the hom-set adjunction iso, packaged as a natural iso of `AddCommGrpCat`-valued functors. -/
noncomputable def adjCoyonedaIso {A B : Type uA} [Category.{v} A] [Category.{v} B]
    [Preadditive A] [Preadditive B] {F : A ⥤ B} {Gf : B ⥤ A} (adj : F ⊣ Gf)
    [F.Additive] [Gf.Additive] (X : A) :
    preadditiveCoyoneda.obj (op (F.obj X)) ≅
      Gf ⋙ preadditiveCoyoneda.obj (op X) :=
  NatIso.ofComponents
    (fun H => AddEquiv.toAddCommGrpIso
      { toEquiv := adj.homEquiv X H
        map_add' := by
          intro a b
          change adj.homEquiv X H (a + b) = adj.homEquiv X H a + adj.homEquiv X H b
          rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
            show Gf.map (a + b) = Gf.map a + Gf.map b from Gf.mapAddHom.map_add a b]
          exact (Preadditive.leftComp _ (adj.unit.app X)).map_add (Gf.map a) (Gf.map b) })
    (by
      intro H H' f
      ext (a : F.obj X ⟶ H)
      change adj.homEquiv X H' (a ≫ f) = (adj.homEquiv X H a) ≫ Gf.map f
      rw [Adjunction.homEquiv_naturality_right])

/-- The "free presheaf on the Yoneda presheaf of `V`": `freeYonedaSheaf V` is its
sheafification. -/
noncomputable abbrev freeYonedaPsh (V : C) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free).obj (yoneda.obj V)

/-- The whiskered `free ⊣ forget` adjunction on presheaf categories. -/
noncomputable abbrev wadj :
    ((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free) ⊣
    ((Functor.whiskeringRight Cᵒᵖ AddCommGrpCat (Type u)).obj (forget AddCommGrpCat)) :=
  AddCommGrpCat.adj.whiskerRight _

/-- The corepresentability bijection `Hom_{Psh}(freeYonedaPsh V, K) ≃ K(op V)` (free-Yoneda),
via the whiskered `free ⊣ forget` adjunction and Yoneda. -/
noncomputable def repEquiv (V : C) (K : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (freeYonedaPsh V ⟶ K) ≃ K.obj (op V) :=
  (wadj.homEquiv (yoneda.obj V) K).trans (yonedaEquiv (X := V) (F := K ⋙ forget AddCommGrpCat))

/-- `Hom_{Psh}(freeYonedaPsh V, -) ≅ evaluation at `op V``, as functors valued in
`AddCommGrpCat`. -/
noncomputable def repIso (V : C) :
    preadditiveCoyoneda.obj (op (freeYonedaPsh V)) ≅
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V) :=
  NatIso.ofComponents
    (fun K => AddEquiv.toAddCommGrpIso
      { toEquiv := repEquiv V K
        map_add' := by
          intro a b
          change repEquiv V K (a + b) = repEquiv V K a + repEquiv V K b
          simp only [repEquiv, Equiv.trans_apply, Adjunction.whiskerRight,
            Adjunction.homEquiv_apply]
          rfl })
    (by
      intro K K' f
      ext (a : freeYonedaPsh V ⟶ K)
      change repEquiv V K' (a ≫ f) = (f.app (op V)) (repEquiv V K a)
      simp only [repEquiv, Equiv.trans_apply]
      rw [Adjunction.homEquiv_naturality_right]
      erw [yonedaEquiv_comp])

/-- **The free-Yoneda corepresentability natural iso.** `Hom_{Sheaf}(L V, -) ≅ (U-)(V)` as functors
`Sheaf J AddCommGrpCat ⥤ AddCommGrpCat`: sheafification adjunction (`adjCoyonedaIso`) composed with
the presheaf corepresentability (`repIso`). -/
noncomputable def eFun (V : C) :
    preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) V)) ≅
      sheafToPresheaf J AddCommGrpCat ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V) :=
  adjCoyonedaIso (sheafificationAdjunction J AddCommGrpCat.{u}) (freeYonedaPsh V) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat) (repIso V)

/-- The sheaf morphism `L g : L Y ⟶ L U` induced by `g : Y ⟶ U`. -/
noncomputable abbrev freeYonedaMap {Y U : C} (g : Y ⟶ U) :
    freeYonedaSheaf (J := J) Y ⟶ freeYonedaSheaf (J := J) U :=
  (presheafToSheaf J AddCommGrpCat).map
    (((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free).map
      (yoneda.map g))

/-- The presheaf-level free-Yoneda morphism `free.map (yoneda.map g)`. -/
noncomputable abbrev freeYonedaPshMap {Y U : C} (g : Y ⟶ U) :
    freeYonedaPsh (C := C) Y ⟶ freeYonedaPsh (C := C) U :=
  ((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free).map
      (yoneda.map g)

/-- Naturality of `repIso` in `V` (presheaf level): precomposition by `free.map (yoneda.map g)`
corresponds to evaluation-restriction along `g`. -/
theorem repIso_naturality {Y U : C} (g : Y ⟶ U) :
    preadditiveCoyoneda.map (Quiver.Hom.op (freeYonedaPshMap (C := C) g)) ≫ (repIso Y).hom
      = (repIso U).hom ≫ (evaluation Cᵒᵖ AddCommGrpCat.{u}).map g.op := by
  ext K (a : freeYonedaPsh U ⟶ K)
  show repEquiv Y K (freeYonedaPshMap g ≫ a) = K.map g.op (repEquiv U K a)
  simp only [repEquiv, Equiv.trans_apply, freeYonedaPshMap]
  rw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality (F := K ⋙ forget AddCommGrpCat) _ g).symm

/-- Naturality of `adjCoyonedaIso` in the object `X` (contravariantly): precomposition by
`F.map φ` on `Hom(F.obj X, -)` corresponds to precomposition by `φ` after `Gf`. -/
theorem adjCoyonedaIso_naturality {A B : Type uA} [Category.{v} A] [Category.{v} B]
    [Preadditive A] [Preadditive B] {F : A ⥤ B} {Gf : B ⥤ A} (adj : F ⊣ Gf)
    [F.Additive] [Gf.Additive] {X' X : A} (φ : X' ⟶ X) :
    preadditiveCoyoneda.map (Quiver.Hom.op (F.map φ)) ≫ (adjCoyonedaIso adj X').hom
      = (adjCoyonedaIso adj X).hom ≫
          Functor.whiskerLeft Gf (preadditiveCoyoneda.map (Quiver.Hom.op φ)) := by
  ext H (a : F.obj X ⟶ H)
  show adj.homEquiv X' H (F.map φ ≫ a) = φ ≫ adj.homEquiv X H a
  rw [Adjunction.homEquiv_naturality_left]

/-- **Naturality of `eFun` in `V` (`(†)` at the level of the corepresentability iso).** -/
theorem eFun_naturality {Y U : C} (g : Y ⟶ U) :
    preadditiveCoyoneda.map (Quiver.Hom.op (freeYonedaMap (J := J) g)) ≫ (eFun (J := J) Y).hom
      = (eFun (J := J) U).hom ≫
          Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat)
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).map g.op) := by
  have hfm : freeYonedaMap (J := J) g
      = (presheafToSheaf J AddCommGrpCat.{u}).map (freeYonedaPshMap (C := C) g) := rfl
  rw [eFun, eFun, Iso.trans_hom, Iso.trans_hom, hfm,
    ← Category.assoc, adjCoyonedaIso_naturality, Category.assoc, Category.assoc]
  congr 1
  rw [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_hom,
    ← Functor.whiskerLeft_comp, repIso_naturality, Functor.whiskerLeft_comp]


/-- **Lemma B + C — free-Yoneda corepresentability, assembled degreewise.** The Hom-complex
`Hom(L V, I^•)` is isomorphic, as a cochain complex (hence on homology), to the section complex
`I^•(V) = (sheafToPresheaf I.cocomplex)(V)`, because `Hom_{Sheaf}(L V, H) ≅ (UH)(V)` naturally in
`H` (free-Yoneda corepresentability): chain `sheafificationAdjunction`
(`Hom(presheafToSheaf.obj P, H) ≅ Hom(P, sheafToPresheaf.obj H)`), the
`AddCommGrpCat.free ⊣ forget` adjunction, and Yoneda (`yonedaEquiv`). Apply this degreewise to
`I^•` (naturally in `H` along the
differentials) to get an iso of complexes, then take `homology n`. The codomain
`((sectionComplex G I).homology n).obj (op V)` is `Hⁿ(I^•(V))` (homology of the section presheaf,
evaluated at `op V`); commuting `homology` past evaluation at `op V` uses
`ShortComplex.mapHomologyIso` with the (exact) evaluation functor, exactly as the kernel-D proof
does for `presheafToSheaf`. -/
noncomputable def homComplexHomologyEquivSectionHomology (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) (V : C) :
    ((homComplex G I V).homology n) ≃+
      ((sectionComplex G I).homology n).obj (op V) :=
  (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
    ((NatIso.mapHomologicalComplex (eFun (J := J) V) (ComplexShape.up ℕ)).app I.cocomplex)) ≪≫
    ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
      ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V))).addCommGroupIsoToAddEquiv

/-- **Bridge (Lemmas A+B+C).** For an injective resolution `I` of
`G`, there is an additive isomorphism `Extⁿ(L V, G) ≃+ Hⁿ(I^•(V))` natural in `V`:
`Ext` is computed by the injective resolution (Lemma A, `extEquivHomComplexHomology`),
`Hom(L V, -)` is the underlying section at `V` (free-Yoneda corepresentability, Lemma B+C,
`homComplexHomologyEquivSectionHomology`), and the bridge is their composite. -/
noncomputable def extEquivSectionHomology (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) (V : C) :
    Abelian.Ext (freeYonedaSheaf (J := J) V) G n ≃+
      ((sectionComplex G I).homology n).obj (op V) :=
  (extEquivHomComplexHomology G I n V).trans (homComplexHomologyEquivSectionHomology G I n V)

/-- The natural transformation `Hom(L U, -) ⟶ Hom(L Y, -)` induced by precomposition with
`L g`, applied to the cocomplex and passed to `homology n`: the middle map of the
naturality square. -/
noncomputable def homComplexMap (G : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution G)
    (n : ℕ) {Y U : C} (g : Y ⟶ U) :
    (homComplex G I U).homology n ⟶ (homComplex G I Y).homology n :=
  (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
    ((NatTrans.mapHomologicalComplex
      (preadditiveCoyoneda.map (Quiver.Hom.op (freeYonedaMap (J := J) g)))
      (ComplexShape.up ℕ)).app I.cocomplex)

/-- The last three factors (B+C+D) of `extEquivHomComplexHomology`: the additive iso
`CohomologyClass (single (L V)) I.cochainComplex n ≃+ H^n(homComplex G I V)` (everything except
the Mathlib `extAddEquivCohomologyClass` factor). By construction
`extEquivHomComplexHomology G I n V = (I.extAddEquivCohomologyClass).trans (factorBCD G I n V)`
(true by `rfl`, see `extEquivHomComplexHomology_eq_factorBCD`). -/
noncomputable def factorBCD (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) (V : C) :
    CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) V)) I.cochainComplex (↑n) ≃+
      ((homComplex G I V).homology n) :=
  ((CochainComplex.HomComplex.homologyAddEquiv
    ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj (freeYonedaSheaf (J := J) V))
    I.cochainComplex (↑n)).symm).trans <|
  (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
    (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) V)
      I.cochainComplex)).addCommGroupIsoToAddEquiv).trans <|
  (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) V)))
    I.cocomplex n).addCommGroupIsoToAddEquiv

/-- `extEquivHomComplexHomology` factors as `extAddEquivCohomologyClass` then `factorBCD`. -/
theorem extEquivHomComplexHomology_eq_factorBCD (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) (V : C) :
    extEquivHomComplexHomology G I n V
      = (I.extAddEquivCohomologyClass).trans (factorBCD G I n V) :=
  rfl

/-- The `CohomologyClass`-level horizontal map of the factor-A naturality square: it is the
unique map making `factorBCD` intertwine it with `homComplexMap`, defined by transporting
`homComplexMap` backward through the additive isomorphism `factorBCD`. (Equivalently, it is
precomposition by `single (L g)` on cohomology classes; see the genuine content lemma
`extAddEquivCohomologyClass_naturality`.) -/
noncomputable def cohClassMap (G : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution G)
    (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (cls : CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) U)) I.cochainComplex (↑n)) :
    CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) Y)) I.cochainComplex (↑n) :=
  (factorBCD G I n Y).symm (homComplexMap G I n g (factorBCD G I n U cls))

/-- **Factor-BCD naturality (glue).** `factorBCD` intertwines `cohClassMap` with
`homComplexMap`. This holds by construction of `cohClassMap` (transport through the iso
`factorBCD`), so it is a formal consequence of `AddEquiv.apply_symm_apply`. -/
theorem factorBCD_naturality (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (cls : CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) U)) I.cochainComplex (↑n)) :
    factorBCD G I n Y (cohClassMap G I n g cls)
      = homComplexMap G I n g (factorBCD G I n U cls) := by
  rw [cohClassMap, AddEquiv.apply_symm_apply]

/-- **Intrinsic `CohomologyClass`-level precomposition by `single (L g)`.** Defined at the
`SmallShiftedHom` level (transport through `CohomologyClass.equivOfIsKInjective`, which is
`toSmallShiftedHom`): precompose a class `cls : CohomologyClass (single (L U)) I.cochainComplex n`
by the single-complex map `single (L g) : single (L Y) ⟶ single (L U)`. Unlike `cohClassMap`,
which is defined by transport through `factorBCD`, this map does not refer to the comparison; the
two are identified by `factorBCD_clPrecomp` below. -/
noncomputable def clPrecomp (G : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution G)
    (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (cls : CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) U)) I.cochainComplex (↑n)) :
    CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) Y)) I.cochainComplex (↑n) :=
  CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.symm
    ((Localization.SmallShiftedHom.mk₀
        (HomologicalComplex.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) 0 rfl
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).map
          (freeYonedaMap (J := J) g))).comp
      (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective cls)
      (by simp))

/-- **Factor-A naturality, intrinsic half.** Mathlib's
`extAddEquivCohomologyClass` is natural in the first `Ext` variable: it intertwines the
`Ext`-precomposition `extRestrict` (precomposition by `L g`) with the intrinsic cohomology-class
precomposition `clPrecomp` (precomposition by `single (L g)`). This is `SmallShiftedHom` algebra
and does not mention `factorBCD`: use
`(extAddEquivCohomologyClass a).toSmallShiftedHom = a.comp (mk₀ R.ι')`
(from `extAddEquivCohomologyClass_apply`, `extEquivCohomologyClass`,
`CohomologyClass.equivOfIsKInjective_apply` and `Equiv.apply_symm_apply`),
`extRestrict = (Ext.mk₀ (L g)).comp ξ`, `Ext.mk₀ φ = SmallShiftedHom.mk₀ _ 0 _ (single φ)` and
`SmallShiftedHom.comp_assoc`, then transport back by injectivity of
`equivOfIsKInjective`. -/
theorem extAddEquivCohomologyClass_naturality_A (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (ξ : Abelian.Ext (freeYonedaSheaf (J := J) U) G n) :
    I.extAddEquivCohomologyClass (extRestrict G n g ξ)
      = clPrecomp G I n g (I.extAddEquivCohomologyClass ξ) := by
  apply CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.injective
  -- reusable fact
  have key : ∀ {X : C} (a : Abelian.Ext (freeYonedaSheaf (J := J) X) G n),
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
          (I.extAddEquivCohomologyClass a)
        = Localization.SmallShiftedHom.comp a (Localization.SmallShiftedHom.mk₀
            (HomologicalComplex.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) 0 rfl
                I.ι')
            (zero_add _) := by
    intro X a
    rw [InjectiveResolution.extAddEquivCohomologyClass_apply,
      InjectiveResolution.extEquivCohomologyClass]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [key]
  -- RHS: clPrecomp
  rw [clPrecomp, Equiv.apply_symm_apply, key]
  -- LHS: extRestrict = (Ext.mk₀ (L g)).comp ξ, push through comp
  rw [extRestrict, Abelian.Ext.comp]
  rw [Localization.SmallShiftedHom.comp_assoc]
  · rfl
  · simp


/-- The coyoneda-side chain map (ℤ-indexed) induced by precomposition with `L g`, applied to
`I.cochainComplex`: `coyoneda(L U).mapHC.obj Ic ⟶ coyoneda(L Y).mapHC.obj Ic`. This is the
ℤ-extension building block of `homComplexMap`. -/
noncomputable def coyonedaPrecompZ (G : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution G)
    {Y U : C} (g : Y ⟶ U) :
    ((preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) U))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.cochainComplex ⟶
      ((preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) Y))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.cochainComplex :=
  (NatTrans.mapHomologicalComplex
    (preadditiveCoyoneda.map (Quiver.Hom.op (freeYonedaMap (J := J) g)))
    (ComplexShape.up ℤ)).app I.cochainComplex

/-- **HomComplex precomposition chain map.** The map
`Hom(single (L U), Ic) ⟶ Hom(single (L Y), Ic)` induced by precomposition with `single (L g)`,
realized via transport of `coyonedaPrecompZ` through `homComplexSingleIsoCoyoneda`. By
construction the factor-C square commutes definitionally. -/
noncomputable def homComplexPrecomp (G : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution G)
    {Y U : C} (g : Y ⟶ U) :
    ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (freeYonedaSheaf (J := J) U)).HomComplex I.cochainComplex ⟶
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (freeYonedaSheaf (J := J) Y)).HomComplex I.cochainComplex :=
  (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) U) I.cochainComplex).hom ≫
    coyonedaPrecompZ G I g ≫
    (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) Y) I.cochainComplex).inv

/-- The intrinsic HomComplex precomposition chain map by a chain map `φ : K' ⟶ K`:
on cochains it is `c ↦ (Cochain.ofHom φ).comp c`. Commutes with the Hom-complex differential
(no sign, since `δ` of a zero-cochain `ofHom φ` vanishes). -/
noncomputable def precompCM {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {K K' L : CochainComplex C' ℤ} (φ : K' ⟶ K) :
    K.HomComplex L ⟶ K'.HomComplex L where
  f i := AddCommGrpCat.ofHom
    { toFun := fun (z : CochainComplex.HomComplex.Cochain K L i) =>
        (CochainComplex.HomComplex.Cochain.ofHom φ).comp z (zero_add i)
      map_zero' := by simp
      map_add' := by intro a b; simp [CochainComplex.HomComplex.Cochain.comp_add] }
  comm' := by
    intro i j hij
    have hij' : i + 1 = j := hij
    ext (z : CochainComplex.HomComplex.Cochain K L i)
    change (CochainComplex.HomComplex.δ i j ((CochainComplex.HomComplex.Cochain.ofHom φ).comp z
        (zero_add i)))
      = (CochainComplex.HomComplex.Cochain.ofHom φ).comp (CochainComplex.HomComplex.δ i j z)
          (zero_add j)
    rw [CochainComplex.HomComplex.δ_zero_cochain_comp _ _ j hij', CochainComplex.HomComplex.δ_ofHom]
    simp

/-- Precomposition by `φ : K' ⟶ K` as an additive map on `n`-cocycles. -/
noncomputable def cocyclePrecomp {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {K K' L : CochainComplex C' ℤ} (φ : K' ⟶ K) (n : ℤ) :
    CochainComplex.HomComplex.Cocycle K L n →+ CochainComplex.HomComplex.Cocycle K' L n where
  toFun z := z.precomp φ
  map_zero' := by ext; simp [CochainComplex.HomComplex.Cocycle.precomp_coe]
  map_add' a b := by ext; simp [CochainComplex.HomComplex.Cocycle.precomp_coe,
    CochainComplex.HomComplex.Cochain.comp_add]

/-- Precomposition sends coboundaries to coboundaries, hence descends to cohomology classes. -/
lemma coboundaries_le_ker {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {K K' L : CochainComplex C' ℤ} (φ : K' ⟶ K) (n : ℤ) :
    CochainComplex.HomComplex.coboundaries K L n
      ≤ ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom K' L n).comp
          (cocyclePrecomp φ n)).ker := by
  intro α hα
  obtain ⟨m, hm, β, hβ⟩ := hα
  rw [AddMonoidHom.mem_ker]
  show CochainComplex.HomComplex.CohomologyClass.mk (α.precomp φ) = 0
  rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff,
    CochainComplex.HomComplex.mem_coboundaries_iff _ m hm]
  refine ⟨(CochainComplex.HomComplex.Cochain.ofHom φ).comp β (zero_add m), ?_⟩
  rw [CochainComplex.HomComplex.Cocycle.precomp_coe,
    CochainComplex.HomComplex.δ_zero_cochain_comp _ _ n hm, CochainComplex.HomComplex.δ_ofHom]
  simp [hβ]

/-- The `commi` square for the left-homology map data of `precompCM φ`. -/
lemma commi_helper {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {K K' L : CochainComplex C' ℤ} (φ : K' ⟶ K) (n : ℤ) :
    AddCommGrpCat.ofHom (cocyclePrecomp φ n) ≫ (CochainComplex.HomComplex.leftHomologyData K' L n).i
      = (CochainComplex.HomComplex.leftHomologyData K L n).i ≫
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
          (precompCM (L := L) φ)).τ₂ := by
  ext (z : CochainComplex.HomComplex.Cocycle K L n)
  show ((z.precomp φ : CochainComplex.HomComplex.Cocycle K' L n) :
      CochainComplex.HomComplex.Cochain K' L n)
      = (CochainComplex.HomComplex.Cochain.ofHom φ).comp (z : CochainComplex.HomComplex.Cochain K L
          n) (zero_add n)
  rw [CochainComplex.HomComplex.Cocycle.precomp_coe]

/-- The `commf'` square for the left-homology map data of `precompCM φ`. -/
lemma commf'_helper {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {K K' L : CochainComplex C' ℤ} (φ : K' ⟶ K) (n : ℤ) :
    (CochainComplex.HomComplex.leftHomologyData K L n).f' ≫ AddCommGrpCat.ofHom (cocyclePrecomp φ n)
      = ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
          (precompCM (L := L) φ)).τ₁ ≫ (CochainComplex.HomComplex.leftHomologyData K' L n).f' := by
  refine (cancel_mono (CochainComplex.HomComplex.leftHomologyData K' L n).i).mp ?_
  rw [Category.assoc, commi_helper (K := K) (K' := K') (L := L) φ n, ← Category.assoc,
    (CochainComplex.HomComplex.leftHomologyData K L n).f'_i,
    ← ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
      (precompCM (L := L) φ)).comm₁₂, Category.assoc,
    (CochainComplex.HomComplex.leftHomologyData K' L n).f'_i]

/-- The left-homology map data of `precompCM φ` realizing `homologyMap (precompCM φ) n` on the
`Cocycle`/`CohomologyClass` model: `φK` is cocycle precomposition, `φH` is class precomposition. -/
noncomputable def precompLHMD {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {K K' L : CochainComplex C' ℤ} (φ : K' ⟶ K) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map (precompCM
          φ))
      (CochainComplex.HomComplex.leftHomologyData K L n)
      (CochainComplex.HomComplex.leftHomologyData K' L n) where
  φK := AddCommGrpCat.ofHom (cocyclePrecomp φ n)
  φH := AddCommGrpCat.ofHom
    (CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom
      ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom K' L n).comp (cocyclePrecomp φ n))
      (coboundaries_le_ker φ n))
  commi := commi_helper φ n
  commf' := commf'_helper φ n
  commπ := by
    ext (z : CochainComplex.HomComplex.Cocycle K L n)
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    rfl

/-- **Homology-level precomposition (intrinsic).** `homologyMap (precompCM φ)` sends the homology
class of a cocycle `z` to the class of `z.precomp φ`, transported through Mathlib's
`homologyAddEquiv`.
This is the genuine `LeftHomologyMapData`-level computation of `homologyMap`. -/
lemma precompCM_homologyAddEquiv_symm {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {K K' L : CochainComplex C' ℤ} (φ : K' ⟶ K) (n : ℤ) (z : CochainComplex.HomComplex.Cocycle K L
        n) :
    HomologicalComplex.homologyMap (precompCM φ) n
        ((CochainComplex.HomComplex.homologyAddEquiv K L n).symm
          (CochainComplex.HomComplex.CohomologyClass.mk z))
      = (CochainComplex.HomComplex.homologyAddEquiv K' L n).symm
          (CochainComplex.HomComplex.CohomologyClass.mk (z.precomp φ)) := by
  have hmap : HomologicalComplex.homologyMap (precompCM φ) n
      = (CochainComplex.HomComplex.leftHomologyData K L n).homologyIso.hom ≫ (precompLHMD φ n).φH
        ≫ (CochainComplex.HomComplex.leftHomologyData K' L n).homologyIso.inv :=
    (precompLHMD φ n).homologyMap_eq
  have hφH : (AddCommGrpCat.Hom.hom (precompLHMD φ n).φH)
      (CochainComplex.HomComplex.CohomologyClass.mk z)
      = CochainComplex.HomComplex.CohomologyClass.mk (z.precomp φ) := by
    show (CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom
        ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom K' L n).comp (cocyclePrecomp φ
            n))
        (coboundaries_le_ker φ n)) (CochainComplex.HomComplex.CohomologyClass.mk z) = _
    rw [CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom_cohomologyClass]; rfl
  show (AddCommGrpCat.Hom.hom (HomologicalComplex.homologyMap (precompCM φ) n))
      ((CochainComplex.HomComplex.leftHomologyData K L n).homologyIso.addCommGroupIsoToAddEquiv.symm
        (CochainComplex.HomComplex.CohomologyClass.mk z))
    = (CochainComplex.HomComplex.leftHomologyData K' L n).homologyIso.addCommGroupIsoToAddEquiv.symm
        (CochainComplex.HomComplex.CohomologyClass.mk (z.precomp φ))
  rw [hmap]
  show (AddCommGrpCat.Hom.hom ((CochainComplex.HomComplex.leftHomologyData K L n).homologyIso.hom
        ≫ (precompLHMD φ n).φH ≫ (CochainComplex.HomComplex.leftHomologyData K' L
            n).homologyIso.inv))
      ((CochainComplex.HomComplex.leftHomologyData K L n).homologyIso.inv
        (CochainComplex.HomComplex.CohomologyClass.mk z))
    = (CochainComplex.HomComplex.leftHomologyData K' L n).homologyIso.inv
        (CochainComplex.HomComplex.CohomologyClass.mk (z.precomp φ))
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, Iso.inv_hom_id_apply, hφH]

/-- **`SmallShiftedHom` precomposition compatibility.** Composing `mk₀ φ` (a degree-0 small shifted
hom) with `mk q s` equals `mk q (φ ≫ s)`. Proved by injectivity of `SmallShiftedHom.equiv` into the
derived category, using `ShiftedHom.mk₀_comp`. -/
lemma smallComp_mk₀_mk {C' : Type uC} [Category.{vC} C'] [Abelian C']
    {X Y Z : CochainComplex C' ℤ} (sg : Y ⟶ X) {n : ℤ} (s : ShiftedHom X Z n)
    [Localization.HasSmallLocalizedShiftedHom (HomologicalComplex.quasiIso C' (ComplexShape.up ℤ))
        ℤ Y X]
    [Localization.HasSmallLocalizedShiftedHom (HomologicalComplex.quasiIso C' (ComplexShape.up ℤ))
        ℤ X Z]
    [Localization.HasSmallLocalizedShiftedHom (HomologicalComplex.quasiIso C' (ComplexShape.up ℤ))
        ℤ Y Z]
    [Localization.HasSmallLocalizedShiftedHom (HomologicalComplex.quasiIso C' (ComplexShape.up ℤ))
        ℤ Z Z] :
    (Localization.SmallShiftedHom.mk₀ (HomologicalComplex.quasiIso C' (ComplexShape.up ℤ)) 0 rfl
        sg).comp
        (Localization.SmallShiftedHom.mk _ s) (add_zero n)
      = Localization.SmallShiftedHom.mk _ (sg ≫ s) := by
  let : HasDerivedCategory C' := HasDerivedCategory.standard C'
  apply (Localization.SmallShiftedHom.equiv (HomologicalComplex.quasiIso C' (ComplexShape.up ℤ))
    (DerivedCategory.Q)).injective
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    Localization.SmallShiftedHom.equiv_mk, Localization.SmallShiftedHom.equiv_mk,
    ShiftedHom.mk₀_comp]
  show DerivedCategory.Q.map sg ≫ ShiftedHom.map s DerivedCategory.Q
    = ShiftedHom.map (sg ≫ s) DerivedCategory.Q
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]

/-- **Obligation D2.** `homComplexPrecomp` (the coyoneda-transport precomposition chain map) equals
the intrinsic `HomComplex` precomposition `precompCM` by `single (L g)`. Proved from the degreewise
naturality of `Cochain.fromSingleEquiv` under precomposition (`Cochain.fromSingleMk_precomp`). -/
lemma factorD2 (G : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution G) {Y U : C} (g : Y ⟶ U) :
    homComplexPrecomp G I g
      = precompCM ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).map
          (freeYonedaMap (J := J) g)) := by
  have hsq :
      precompCM ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).map (freeYonedaMap (J
          := J) g))
          ≫ (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) Y) I.cochainComplex).hom
        = (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) U) I.cochainComplex).hom
            ≫ coyonedaPrecompZ G I g := by
    ext j (c : CochainComplex.HomComplex.Cochain _ _ j)
    obtain ⟨f, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective c j (by ring)
    simp only [HomologicalComplex.comp_f, homComplexSingleIsoCoyoneda, coyonedaPrecompZ, precompCM,
      HomologicalComplex.Hom.isoOfComponents_hom_f, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
      AddEquiv.toAddCommGrpIso_hom, AddEquiv.coe_toAddMonoidHom,
      NatTrans.mapHomologicalComplex_app_f, AddCommGrpCat.hom_ofHom]
    show (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0:ℤ)+j=j))
        ((CochainComplex.HomComplex.Cochain.ofHom
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).map (freeYonedaMap (J :=
                J) g))).comp
          (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+j=j)) (zero_add j))
      = freeYonedaMap (J := J) g ≫ (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring :
          (0:ℤ)+j=j))
          (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+j=j))
    rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_precomp,
      CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
      CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  rw [homComplexPrecomp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Factor D, the analytic kernel of the naturality.** The Mathlib comparison `homologyAddEquiv`
intertwines the cohomology-class precomposition `clPrecomp g` (precomposition by `single (L g)`,
defined at the `SmallShiftedHom` level) with `homologyMap` of the Hom-complex precomposition chain
map `homComplexPrecomp g`. This is a `SmallShiftedHom`/`Cocycle`-level compatibility of
`equivOfIsKInjective`/`homologyAddEquiv` with precomposition, not a consequence of
`extEquivHomComplexHomology_naturality`, so the argument is not circular. -/
theorem factorD_clPrecomp (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (cls : CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) U)) I.cochainComplex (↑n)) :
    (CochainComplex.HomComplex.homologyAddEquiv
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) Y)) I.cochainComplex (↑n)).symm
        (clPrecomp G I n g cls)
      = HomologicalComplex.homologyMap (homComplexPrecomp G I g) (↑n)
          ((CochainComplex.HomComplex.homologyAddEquiv
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
              (freeYonedaSheaf (J := J) U)) I.cochainComplex (↑n)).symm cls) := by
  apply (CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (freeYonedaSheaf (J := J) Y)) I.cochainComplex (↑n)).injective
  rw [AddEquiv.apply_symm_apply]
  apply CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.injective
  rw [clPrecomp, Equiv.apply_symm_apply]
  -- Pick a cocycle representative of `cls`.
  obtain ⟨z, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective cls
  -- D2: replace the coyoneda-transport precomposition by the intrinsic one, then compute homology.
  rw [factorD2,
    precompCM_homologyAddEquiv_symm
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).map (freeYonedaMap (J := J) g))
          (↑n) z,
    AddEquiv.apply_symm_apply]
  -- Both sides are now `equivOfIsKInjective` of cohomology classes; convert to
  -- `SmallShiftedHom.mk`.
  rw [CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective_apply,
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective_apply,
    CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom_mk,
    CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom_mk,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
    smallComp_mk₀_mk]

/-- Auxiliary: `auxIso` transported along an equality of `Option`-indices, expressed via
`eqToHom` conjugation. -/
lemma auxIso_hom_congr
    {C' D : Type uC} [Category.{vC} C'] [Category.{vC} D] [Abelian C'] [Abelian D]
    (F : C' ⥤ D) [F.Additive] (X : CochainComplex C' ℕ) {o o' : Option ℕ} (h : o = o') :
    (auxIso F X o).hom = eqToHom (by rw [h]) ≫ (auxIso F X o').hom ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Auxiliary: a natural transformation's component transported along an equality of objects,
expressed via `eqToHom` conjugation. -/
lemma tau_app_congr
    {C' D : Type uC} [Category.{vC} C'] [Category.{vC} D]
    {F F' : C' ⥤ D} (τ : F ⟶ F') {Y Z : C'}
    (h : Y = Z) (p1 : F.obj Y = F.obj Z) (p2 : F'.obj Z = F'.obj Y) :
    τ.app Y = eqToHom p1 ≫ τ.app Z ≫ eqToHom p2 := by
  subst h; simp

/-- **Factor B, chain-level helper.** Naturality of `mapExtendIso` in the additive-functor
variable along `τ : F ⟶ F'`: the comparison `mapExtendIso` intertwines `mapHomologicalComplex τ`
(ℤ-level, on the extension) with `extendMap` of `mapHomologicalComplex τ` (ℕ-level). The `none`
component is handled by the zero object; the `some a` component is the naturality of `τ` conjugated
by the `extend.XIso` identifications. -/
lemma mapExtendIso_naturality
    {C' D : Type uC} [Category.{vC} C'] [Category.{vC} D] [Abelian C'] [Abelian D]
    {F F' : C' ⥤ D} [F.Additive] [F'.Additive] (τ : F ⟶ F') (X : CochainComplex C' ℕ) :
    (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        (HomologicalComplex.extend X ComplexShape.embeddingUpNat) ≫ (mapExtendIso F' X).hom
      = (mapExtendIso F X).hom ≫
        HomologicalComplex.extendMap
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app X)
          ComplexShape.embeddingUpNat := by
  ext i'
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [mapExtendIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    NatTrans.mapHomologicalComplex_app_f]
  show τ.app (HomologicalComplex.extend.X X (ComplexShape.embeddingUpNat.r i')) ≫
      (auxIso F' X (ComplexShape.embeddingUpNat.r i')).hom = _
  obtain (h | ⟨a, ha⟩) := (ComplexShape.embeddingUpNat.r i').eq_none_or_eq_some
  · exact (HomologicalComplex.extend.isZero_X
      ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj X) h).eq_of_tgt _ _
  · have hf : ComplexShape.embeddingUpNat.f a = i' :=
      ComplexShape.embeddingUpNat.f_eq_of_r_eq_some ha
    subst hf
    rw [HomologicalComplex.extendMap_f _ _ rfl]
    rw [auxIso_hom_congr F X ha, auxIso_hom_congr F' X ha]
    simp only [auxIso, HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      NatTrans.mapHomologicalComplex_app_f,
      eqToHom_trans, eqToHom_map]
    have hY : HomologicalComplex.extend.X X
        (ComplexShape.embeddingUpNat.r (ComplexShape.embeddingUpNat.f a)) = X.X a := by rw [ha]; rfl
    rw [tau_app_congr τ hY (by rw [hY]) (by rw [hY])]
    generalize_proofs i1 i2 i3 i4 i5 i6 o1 o2 o3 i7 o4 o5 o6
    have m1 : eqToHom o4 ≫ eqToHom o5 = eqToHom o1 := by rw [eqToHom_trans]
    have m2 : eqToHom o2 ≫ eqToHom o3 = eqToHom o6 := by rw [eqToHom_trans]
    rw [Category.assoc, Category.assoc, m2]
    conv_rhs => rw [← Category.assoc]
    exact (congrArg (· ≫ τ.app (X.X a) ≫ eqToHom o6) m1).symm

set_option maxHeartbeats 1600000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- **Factor C + B (glue).** The last two factors of `factorBCD` (the
`homComplexSingleIsoCoyoneda` factor C and the `mapExtendHomologyIso` factor B) intertwine
`homologyMap (homComplexPrecomp g)` with `homComplexMap g`. Factor C is definitional (by
construction of `homComplexPrecomp` as the transport of `coyonedaPrecompZ`) plus `homologyMap`
functoriality; factor B is the naturality of `mapExtendHomologyIso` in the additive-functor
variable along `preadditiveCoyoneda.map (op (L g))`. -/
theorem factorCB_homComplexMap (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (x : ((HomologicalComplex.homologyFunctor (AddCommGrpCat.{u}) (ComplexShape.up ℤ) (n : ℤ)).obj
        (((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) U)).HomComplex I.cochainComplex))) :
    ((((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
        (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) Y)
          I.cochainComplex)).addCommGroupIsoToAddEquiv).trans
      (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) Y)))
        I.cocomplex n).addCommGroupIsoToAddEquiv)
        (HomologicalComplex.homologyMap (homComplexPrecomp G I g) (↑n) x)
      = homComplexMap G I n g
          (((((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
            (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) U)
              I.cochainComplex)).addCommGroupIsoToAddEquiv).trans
          (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) U)))
            I.cocomplex n).addCommGroupIsoToAddEquiv) x) := by
  have hmor :
      HomologicalComplex.homologyMap (homComplexPrecomp G I g) (↑n) ≫
          ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
            (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) Y) I.cochainComplex)).hom ≫
          (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) Y)))
            I.cocomplex n).hom
        = ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
            (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) U) I.cochainComplex)).hom ≫
          (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) U)))
            I.cocomplex n).hom ≫
          homComplexMap G I n g := by
    -- Factor C: definitional + homologyMap functoriality + inv_hom_id cancellation.
    have hC :
        HomologicalComplex.homologyMap (homComplexPrecomp G I g) (↑n) ≫
          ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
              (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) Y) I.cochainComplex)).hom
          = ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n:ℤ)).mapIso
              (homComplexSingleIsoCoyoneda (freeYonedaSheaf (J := J) U) I.cochainComplex)).hom ≫
            HomologicalComplex.homologyMap (coyonedaPrecompZ G I g) (↑n) := by
      rw [homComplexPrecomp, Functor.mapIso_hom, Functor.mapIso_hom,
        HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyFunctor_map,
        HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
        Category.assoc, Category.assoc, ← HomologicalComplex.homologyMap_comp,
        Iso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.comp_id]
    -- Factor B: naturality of mapExtendHomologyIso in the additive-functor variable.
    have hB :
        HomologicalComplex.homologyMap (coyonedaPrecompZ G I g) (↑n) ≫
            (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) Y)))
              I.cocomplex n).hom
          = (mapExtendHomologyIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) U)))
              I.cocomplex n).hom ≫
            homComplexMap G I n g := by
      have hnat := mapExtendIso_naturality
        (preadditiveCoyoneda.map (Quiver.Hom.op (freeYonedaMap (J := J) g))) I.cocomplex
      rw [coyonedaPrecompZ, mapExtendHomologyIso, mapExtendHomologyIso, Iso.trans_hom,
        Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
        HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyFunctor_map,
        ← Category.assoc, ← HomologicalComplex.homologyMap_comp]
      rw [show (NatTrans.mapHomologicalComplex
            (preadditiveCoyoneda.map (Quiver.Hom.op (freeYonedaMap (J := J) g)))
            (ComplexShape.up ℤ)).app I.cochainComplex ≫
              (mapExtendIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) Y)))
                I.cocomplex).hom
          = (mapExtendIso (preadditiveCoyoneda.obj (op (freeYonedaSheaf (J := J) U)))
                I.cocomplex).hom ≫
              HomologicalComplex.extendMap
                ((NatTrans.mapHomologicalComplex
                  (preadditiveCoyoneda.map (Quiver.Hom.op (freeYonedaMap (J := J) g)))
                  (ComplexShape.up ℕ)).app I.cocomplex) ComplexShape.embeddingUpNat
          from hnat,
        HomologicalComplex.homologyMap_comp, Category.assoc,
        HomologicalComplex.extendHomologyIso_hom_naturality, ← Category.assoc]
      rfl
    rw [Functor.mapIso_hom, Functor.mapIso_hom] at hC ⊢
    rw [← Category.assoc, hC, Category.assoc, hB]
  exact ConcreteCategory.congr_hom hmor x

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- **Factors B+C+D together.** The composite comparison `factorBCD` intertwines the
cohomology-class precomposition `clPrecomp g` with the Hom-complex-homology map
`homComplexMap g`: chain factor D (`factorD_clPrecomp`) with factors C and B
(`factorCB_homComplexMap`). -/
theorem factorBCD_clPrecomp (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (cls : CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (freeYonedaSheaf (J := J) U)) I.cochainComplex (↑n)) :
    factorBCD G I n Y (clPrecomp G I n g cls)
      = homComplexMap G I n g (factorBCD G I n U cls) := by
  -- factorBCD V = D_V.trans (C_V.trans B_V) where D_V = homologyAddEquiv.symm.
  -- Chain factor D (factorD_clPrecomp) then factors C+B (factorCB_homComplexMap).
  rw [factorBCD, factorBCD, AddEquiv.trans_apply, AddEquiv.trans_apply,
    factorD_clPrecomp G I n g cls]
  exact factorCB_homComplexMap G I n g _

/-- **Factor-A naturality.** Mathlib's `extAddEquivCohomologyClass`
intertwines the `Ext`-precomposition `extRestrict` with the cohomology-class map `cohClassMap`.
Assembled, non-circularly, from `extAddEquivCohomologyClass_naturality_A` (pure
`SmallShiftedHom`) and `factorBCD_clPrecomp` (the `factorBCD`-factor naturalities):
`cohClassMap g (eq ξ) = (factorBCD Y).symm (homComplexMap g (factorBCD U (eq ξ)))
  = (factorBCD Y).symm (factorBCD Y (clPrecomp g (eq ξ))) = clPrecomp g (eq ξ)
  = eq (extRestrict g ξ)`. -/
theorem extAddEquivCohomologyClass_naturality (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (ξ : Abelian.Ext (freeYonedaSheaf (J := J) U) G n) :
    I.extAddEquivCohomologyClass (extRestrict G n g ξ)
      = cohClassMap G I n g (I.extAddEquivCohomologyClass ξ) := by
  rw [extAddEquivCohomologyClass_naturality_A, cohClassMap, ← factorBCD_clPrecomp,
    AddEquiv.symm_apply_apply]

/-- `(∗)`: the Ext-resolution comparison `extEquivHomComplexHomology` intertwines the
Ext-precomposition `extRestrict` with the Hom-complex-homology map `homComplexMap`. -/
theorem extEquivHomComplexHomology_naturality (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (ξ : Abelian.Ext (freeYonedaSheaf (J := J) U) G n) :
    extEquivHomComplexHomology G I n Y (extRestrict G n g ξ)
      = homComplexMap G I n g (extEquivHomComplexHomology G I n U ξ) := by
  rw [extEquivHomComplexHomology_eq_factorBCD, extEquivHomComplexHomology_eq_factorBCD,
    AddEquiv.trans_apply, AddEquiv.trans_apply,
    extAddEquivCohomologyClass_naturality G I n g ξ, factorBCD_naturality]

/-- **Sub-lemma (∗∗) — naturality of `ShortComplex.mapHomologyIso` in the *functor* variable.**
For the section complex `sectionComplex G I` and `g : Y ⟶ U`, the comparison iso
`ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
((evaluation Cᵒᵖ AddCommGrpCat).obj (op V))`
(homology commutes with evaluation at `op V`) is natural as the evaluation point varies along `g`:
the homology-of-(whiskered evaluation-restriction map) intertwines with the presheaf restriction
`((sectionComplex G I).homology n).map g.op`. Mathlib packages `mapHomologyIso_hom_naturality`
only in the short-complex variable; this is the functor-variable companion, obtained by unfolding
`ShortComplex.mapHomologyIso` through the naturality `ShortComplex.homologyMap_mapNatTrans` of
the evaluation natural transformation `ev.map g.op`. -/
theorem mapHomologyIso_evaluation_naturality
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max u v})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U) :
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex
            (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{max u v})
              ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).map g.op)) (ComplexShape.up ℕ)).app
                I.cocomplex) ≫
        (ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
          ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op Y))).hom
      = (ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
          ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U))).hom ≫
        ((sectionComplex G I).homology n).map g.op := by
  set S := (sectionComplex G I).sc n with hS
  set α := (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).map g.op with hα
  have key := ShortComplex.homologyMap_mapNatTrans S α
  rw [HomologicalComplex.homologyFunctor_map,
    show HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{max u v}) α)
            (ComplexShape.up ℕ)).app
            I.cocomplex) n
      = ShortComplex.homologyMap (S.mapNatTrans α) from rfl, key,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- Morphism-level `(†)`: the naturality square of `homComplexHomologyEquivSectionHomology`
as `AddCommGrpCat`-morphisms. -/
theorem homComplexHomologyEquivSectionHomology_naturality_hom (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U) :
    homComplexMap G I n g ≫
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
          ((NatIso.mapHomologicalComplex (eFun (J := J) Y) (ComplexShape.up ℕ)).app I.cocomplex) ≪≫
          ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op Y))).hom
      = ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
          ((NatIso.mapHomologicalComplex (eFun (J := J) U) (ComplexShape.up ℕ)).app I.cocomplex) ≪≫
          ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).hom ≫
          ((sectionComplex G I).homology n).map g.op := by
  -- `βV.hom = NatTrans.mapHomologicalComplex (eFun V).hom`, applied at `I.cocomplex`.
  -- Step 1: lift `eFun_naturality` through `NatTrans.mapHomologicalComplex` and `homologyFunctor`.
  have hstep1 :
      homComplexMap G I n g ≫
          (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
            ((NatIso.mapHomologicalComplex (eFun (J := J) Y) (ComplexShape.up ℕ)).app
                I.cocomplex).hom
        = (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
            ((NatIso.mapHomologicalComplex (eFun (J := J) U) (ComplexShape.up ℕ)).app
                I.cocomplex).hom ≫
          (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
            ((NatTrans.mapHomologicalComplex
              (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat)
                ((evaluation Cᵒᵖ AddCommGrpCat.{u}).map g.op)) (ComplexShape.up ℕ)).app
              I.cocomplex) := by
    rw [homComplexMap, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    have he : ((NatIso.mapHomologicalComplex (eFun (J := J) Y) (ComplexShape.up ℕ)).app
          I.cocomplex).hom
        = (NatTrans.mapHomologicalComplex (eFun (J := J) Y).hom (ComplexShape.up ℕ)).app
            I.cocomplex := rfl
    have heU : ((NatIso.mapHomologicalComplex (eFun (J := J) U) (ComplexShape.up ℕ)).app
          I.cocomplex).hom
        = (NatTrans.mapHomologicalComplex (eFun (J := J) U).hom (ComplexShape.up ℕ)).app
            I.cocomplex := rfl
    rw [he, heU, ← NatTrans.comp_app, ← NatTrans.comp_app,
      ← NatTrans.mapHomologicalComplex_comp, ← NatTrans.mapHomologicalComplex_comp,
      eFun_naturality]
  have hstep2 :
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
            ((NatTrans.mapHomologicalComplex
              (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat)
                ((evaluation Cᵒᵖ AddCommGrpCat.{u}).map g.op)) (ComplexShape.up ℕ)).app
                    I.cocomplex) ≫
          (ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op Y))).hom
        = (ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).hom ≫
          ((sectionComplex G I).homology n).map g.op :=
    mapHomologyIso_evaluation_naturality G I n g
  rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    ← Category.assoc, hstep1, Category.assoc, hstep2, Category.assoc]

/-- `(†)`: the free-Yoneda corepresentability iso `homComplexHomologyEquivSectionHomology`
intertwines the Hom-complex-homology map `homComplexMap` with the section-cohomology
restriction `(homology n).map g.op`. -/
theorem homComplexHomologyEquivSectionHomology_naturality (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (η : (homComplex G I U).homology n) :
    homComplexHomologyEquivSectionHomology G I n Y (homComplexMap G I n g η)
      = ((sectionComplex G I).homology n).map g.op
          (homComplexHomologyEquivSectionHomology G I n U η) := by
  exact ConcreteCategory.congr_hom
    (homComplexHomologyEquivSectionHomology_naturality_hom G I n g) η

/-- Naturality of the bridge `extEquivSectionHomology` along `g : Y ⟶ U`: it intertwines
the `Ext`-precomposition `extRestrict` with the section-cohomology restriction
`(homology n).map g.op`. -/
theorem extEquivSectionHomology_naturality (G : Sheaf J AddCommGrpCat.{u})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (ξ : Abelian.Ext (freeYonedaSheaf (J := J) U) G n) :
    extEquivSectionHomology G I n Y (extRestrict G n g ξ)
      = ((sectionComplex G I).homology n).map g.op (extEquivSectionHomology G I n U ξ) := by
  simp only [extEquivSectionHomology, AddEquiv.trans_apply]
  rw [extEquivHomComplexHomology_naturality G I n g ξ,
    homComplexHomologyEquivSectionHomology_naturality G I n g]

/-- **Lemma D, the analytic kernel of 01FW.** For an injective resolution `I` of `G` and `n > 0`,
the `n`-th homology *presheaf* of the section complex `I^•(-)` is locally zero: every section
`η` over `U` is killed on a covering `S` of `U`. Proof: the *sheaf* cohomology of `I^•`
vanishes in degree `n > 0` (it is a resolution), and presheaf cohomology sheafifies
to sheaf cohomology by exactness of sheafification, so the presheaf `Hⁿ(I^•(-))`
has zero sheafification; finally a section with zero image in the sheafification dies on a
cover, via `GrothendieckTopology.Plus.eq_mk_iff_exists` /
`Presheaf.isLocallySurjective_toSheafify`. Works entirely in the `.{u}` universe (no
sheafification of `G.cohomologyPresheaf n`, which is `.{w}`). -/
@[sga "4 V 3.1" "special case"]
theorem injectiveResolution_homology_presheaf_locally_zero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    (G : Sheaf J AddCommGrpCat.{max u v}) (I : InjectiveResolution G) (n : ℕ) (hn : 0 < n)
    (U : C) (η : ((sectionComplex G I).homology n).obj (op U)) :
    ∃ S : J.Cover U, ∀ g : S.Arrow,
      ((sectionComplex G I).homology n).map g.f.op η = 0 := by
  -- Abbreviate the homology presheaf `P = Hⁿ(I^•(-))`.
  let P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} := (sectionComplex G I).homology n
  show ∃ S : J.Cover U, ∀ g : S.Arrow, P.map g.f.op η = 0
  -- The sheafification of `P` is the zero sheaf: applying the exact functor
  -- `presheafToSheaf` to `P` recovers the (degree `n>0`, hence zero) homology of the
  -- exact complex of sheaves `I.cocomplex`.
  have hz : IsZero ((presheafToSheaf J AddCommGrpCat.{max u v}).obj P) := by
    have e1 : (presheafToSheaf J AddCommGrpCat.{max u v}).obj P ≅
        (((presheafToSheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex _).obj
          (sectionComplex G I)).homology n :=
      (ShortComplex.mapHomologyIso ((sectionComplex G I).sc n)
        (presheafToSheaf J AddCommGrpCat.{max u v})).symm
    have ecpx : ((presheafToSheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (sectionComplex G I) ≅ I.cocomplex := by
      refine (?_ : _ ≅ ((𝟭 (Sheaf J AddCommGrpCat.{max u v})).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) ≪≫ ?_
      · exact ((NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{max u v})
          (ComplexShape.up ℕ)).app I.cocomplex).symm
      · exact (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℕ)).app I.cocomplex
    have e2 : (((presheafToSheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex _).obj
          (sectionComplex G I)).homology n ≅ I.cocomplex.homology n :=
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso ecpx
    have ezero : IsZero (I.cocomplex.homology n) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      exact I.cocomplex_exactAt_succ m
    exact IsZero.of_iso ezero (e1 ≪≫ e2)
  -- The section `η` maps to `0` in the (zero) sheafification of `P`.
  have h0 : (toSheafify J P).app (op U) η = 0 := by
    have hzsh : IsZero (sheafify J P) :=
      Functor.map_isZero (sheafToPresheaf J AddCommGrpCat.{max u v}) hz
    have hzU : IsZero ((sheafify J P).obj (op U)) :=
      Functor.map_isZero ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)) hzsh
    have hsub : Subsingleton ((sheafify J P).obj (op U)) := by
      rw [AddCommGrpCat.isZero_iff_subsingleton] at hzU; exact hzU
    apply Subsingleton.elim
  -- Local injectivity of the unit `toSheafify` turns "dies in the sheafification"
  -- into "dies on a cover": the equalizer sieve of `η` and `0` is `J`-covering.
  have hli : Presheaf.IsLocallyInjective J (toSheafify J P) := inferInstance
  have hmem : Presheaf.equalizerSieve (F := P) (X := op U) η 0 ∈ J U := by
    apply hli.equalizerSieve_mem η 0
    simp [h0]
  refine ⟨⟨_, hmem⟩, fun g => ?_⟩
  have hg := g.hf
  simp only [Presheaf.equalizerSieve] at hg
  rw [hg, map_zero]

/-- **Analytic kernel, Ext-native form.** For `n > 0`,
every positive-degree `Ext` class `ξ : Ext (L U) G n` out of the local generator
`L U = freeYonedaSheaf U` is killed, over some covering `S` of `U`, by precomposition with
`L g.f` for each member `g : S.Arrow`. Equivalently: the presheaf `V ↦ Extⁿ(L V, G)`
(`= G.cohomologyPresheaf n`) is locally zero for `n > 0`.

The proof transports `ξ` through the bridge `Extⁿ(L U, G) ≃+ Hⁿ(I^•(U))` for a chosen
injective resolution `I` of `G`, applies the kernel lemma
`injectiveResolution_homology_presheaf_locally_zero` to get the cover, and pulls the
vanishing back via the naturality of the bridge and its injectivity. -/
theorem ext_generator_locally_zero (G : Sheaf J AddCommGrpCat)
    (n : ℕ) (hn : 0 < n) (U : C) (ξ : Abelian.Ext (freeYonedaSheaf (J := J) U) G n) :
    ∃ S : J.Cover U, ∀ g : S.Arrow,
      (Abelian.Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free).map
          (yoneda.map g.f)))).comp ξ (zero_add n) = 0 := by
  -- Choose an injective resolution of `G` (enough injectives on the small site).
  obtain ⟨I⟩ : Nonempty (InjectiveResolution G) := ⟨InjectiveResolution.of G⟩
  -- Transport `ξ` to `η` in the section-cohomology presheaf and apply the kernel lemma.
  obtain ⟨S, hS⟩ :=
    injectiveResolution_homology_presheaf_locally_zero G I n hn U
      (extEquivSectionHomology G I n U ξ)
  refine ⟨S, fun g => ?_⟩
  show extRestrict G n g.f ξ = 0
  -- The bridge at `g.Y` sends the goal class to the kernel value `0`; conclude by injectivity.
  refine (extEquivSectionHomology G I n g.Y).injective ?_
  simpa [extEquivSectionHomology_naturality G I n g.f ξ] using hS g

/-- **The cohomology presheaf is locally zero in positive degree.** For `n > 0`, every class
`ξ ∈ Hⁿ(U, G) = (G.cohomologyPresheaf n).obj (op U)` is killed by restriction along the members
of some covering of `U`. This is `ext_generator_locally_zero` read through the definitional
description of `G.cohomologyPresheaf n` as `V ↦ Extⁿ(L V, G)`. -/
theorem cohomologyPresheaf_locally_zero (G : Sheaf J AddCommGrpCat)
    (n : ℕ) (hn : 0 < n) (U : C) (ξ : (G.cohomologyPresheaf n).obj (op U)) :
    ∃ S : J.Cover U, ∀ g : S.Arrow,
      (G.cohomologyPresheaf n).map g.f.op ξ = 0 := by
  -- Mathlib defines
  --   `G.cohomologyPresheaf n = ((yoneda ⋙ free ⋙ presheafToSheaf).op ⋙ extFunctor n).flip`,
  -- so writing `L V = freeYonedaSheaf V = presheafToSheaf.obj (free.obj (yoneda.obj V))`,
  -- we have *definitionally*:
  --   `(G.cohomologyPresheaf n).obj (op U)   = Abelian.Ext (L U) G n`, and
  --   `(G.cohomologyPresheaf n).map g.f.op ξ = (Ext.mk₀ (L g.f)).comp ξ (zero_add n)`.
  -- Hence this goal is defeq to `ext_generator_locally_zero`, applied below.
  let ξ' : Abelian.Ext (freeYonedaSheaf (J := J) U) G n := ξ
  obtain ⟨S, hS⟩ := ext_generator_locally_zero G n hn U ξ'
  exact ⟨S, hS⟩

/-- **Stacks Project, Tag 01FW (Lemma 21.7.3).** Locality of cohomology.

Let `(C, O)` be a ringed site (with `O = R : Sheaf J RingCat`), let `F` be a sheaf
of `O`-modules, let `U` be an object of `C`, let `n > 0` and let
`ξ ∈ H^n(U, F)`. Then there exists a covering `{U_i -> U}` of `U` such that the
restriction `ξ|_{U_i}` vanishes in `H^n(U_i, F)` for every member `i` of the
covering. -/
@[stacks 01FW]
theorem locality_of_cohomology (R : Sheaf J RingCat) (F : SheafOfModules R)
    (n : ℕ) (hn : 0 < n) (U : C) (ξ : cohomology R F n U) :
    ∃ S : J.Cover U, ∀ g : S.Arrow,
      (restriction R F n g.f) ξ = 0 := by
  -- Unfold `restriction` to the cohomology-presheaf map (`restriction_apply`, `rfl`)
  -- and apply the generic locality lemma to the underlying abelian sheaf of `F`.
  obtain ⟨S, hS⟩ :=
    cohomologyPresheaf_locally_zero ((SheafOfModules.toSheaf R).obj F) n hn U ξ
  refine ⟨S, fun g => ?_⟩
  rw [restriction_apply]
  exact hS g

end Stacks.Cohomology.Locality
