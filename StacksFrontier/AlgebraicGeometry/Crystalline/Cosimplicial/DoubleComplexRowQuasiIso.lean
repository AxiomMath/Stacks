module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRowComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.EndomorphismFactorizationQuasiIso

/-!
# The rowwise hypothesis of [Stacks, Tag 07LG] from a homotopy equivalence of the rows

The rowwise hypothesis `hrows` of `...SmallSite.computes07LG_of_doubleComplex` asks that each row
map

`(StacksDraft.TotalRowComparison.flipMap (cosimplicialDoubleComplexFunctor.map rho)).f b`

of a comparison `rho : K ⟶ Const(R)` be a `QuasiIso`, for every `b : ℤ`.  What the completed
clause of [Stacks, Lemma 60.21.2, Tag 07LD] produces —
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` and its instantiation
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_pushedConnection` — is of a
different kind: a *section* `ι' : R ⟶ K^{*,b}` of the row map together with a retraction and a
chain homotopy, all in the `ℕ`-indexed world of the rows themselves, with no reference to the
double complex or to its two `ℕ`-to-`ℤ` extensions.

This module bridges the two.  It is pure homological algebra: nothing here mentions divided
powers, a crystal or a connection.

## The three steps

* **The row of a morphism.**  `Crystalline.cosimplicialRowComplex` is the row `b` of a cochain
  complex of cosimplicial groups, and it is the value of a functor, so a morphism `rho` has a row
  `Crystalline.cosimplicialRowMap rho b`, the family `(rho.f a).app ⦋b⦌`.

* **The rows of the double complex, naturally.**
  `Crystalline.cosimplicialDoubleComplexRowIso` identifies the row `b` of the double complex with
  the `ℕ`-to-`ℤ` extension of the row `b` of `K`, and
  `Crystalline.cosimplicialDoubleComplexRowIso_naturality` says that identification is natural in
  `K`.  Both halves of the naturality are available already — extending commutes with applying a
  functor degreewise naturally in the complex
  (`HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality`), and the absorption of the
  inner extension is a natural transformation applied degreewise
  (`ComplexShape.Embedding.extendFunctorCompEvalIso`) — so the proof is their composition, and no
  case analysis on the sign of the exterior degree is needed.  The extension itself neither
  creates nor destroys quasi-isomorphisms, which is Mathlib's
  `HomologicalComplex.quasiIso_extendMap_iff`.

* **From a section to a quasi-isomorphism.**  A map with a section which is a quasi-isomorphism is
  one itself, which is `Crystalline.CompletedDeRham.quasiIso_of_section`.  This is what makes the
  asymmetry harmless: the perturbation lemma produces the comparison in the direction
  `R = M ⊗^∧_D Ω^*_D ⟶ M ⊗^∧_D Ω^*_{D(b)} = K^{*,b}`, whereas `rho` runs the other way, being
  induced by the codiagonal `ε_b : D(b) → D`; and `ε_b` retracts each coprojection
  (`Crystalline.completedEnvelopeCodiagonal_coprojection`), which is exactly the hypothesis
  `iota ≫ rho = 𝟙` below.

## Main results

* `Crystalline.cosimplicialDoubleComplexRowIso_naturality` — **the identification of the rows of
  the double complex with the rows of `K` is natural in `K`.**
* `Crystalline.quasiIso_flipMap_of_quasiIso_row` — **the rowwise hypothesis from the rows**: if
  the row `b` of `rho` is a quasi-isomorphism for every `b : ℕ` then every row map of the double
  complex is one.  The rows indexed by a negative integer need no hypothesis, both sides vanishing
  there.  `Crystalline.quasiIso_row_of_quasiIso_flipMap` is the converse, so the two hypotheses are
  equivalent.
* `Crystalline.quasiIso_flipMap_of_rowHomotopyEquiv` and
  `Crystalline.quasiIso_flipMap_of_rowDegreewiseHomotopyEquiv` — **the rowwise hypothesis from a
  homotopy equivalence of each row with `R`**, the second with the homotopy given as a
  degree-lowering family and the two contraction identities, which is the shape the perturbation
  lemma produces.

## Implementation notes

**No tag attribute is placed: nothing here is the content of a tag.** Identifying the row `b` of
the crystalline `K` with `M ⊗̂_D Ω̂^*_{D(b)}`, and `D(b)` with a divided power polynomial
completion over `D`, is not done here; this module takes the homotopy equivalence as a hypothesis
about the rows as they stand.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial

universe u

namespace Crystalline

namespace CompletedDeRham

/-- **A map with a section which is a quasi-isomorphism is a quasi-isomorphism.**

If `iota ≫ rho = 𝟙` and `iota` is a quasi-isomorphism then so is `rho`: the composite is the
identity, hence a quasi-isomorphism, and a quasi-isomorphism can be cancelled on the left.

This is how the output of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` is read in the
direction the rowwise hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] needs it: the
perturbation lemma produces `ι' : M ⊗^∧_D Ω^*_D ⟶ M ⊗^∧_D Ω^*_{D'}`, and the quasi-isomorphism
asked for runs the other way, being induced by the codiagonal, which retracts the coprojection. -/
public theorem quasiIso_of_section {X Y : CochainComplex AddCommGrpCat.{u} ℕ} (iota : X ⟶ Y)
    (rho : Y ⟶ X) (hsec : iota ≫ rho = 𝟙 X) [QuasiIso iota] : QuasiIso rho := by
  have : QuasiIso (iota ≫ rho) := by rw [hsec]; infer_instance
  exact quasiIso_of_comp_left iota rho

/-- **A degreewise homotopy retract is a quasi-isomorphism**, which is
`Crystalline.CompletedDeRham.isIso_homologyMap_of_degreewiseHomotopyRetract` read as a `QuasiIso`
rather than degree by degree. -/
public theorem quasiIso_of_degreewiseHomotopyRetract {X Y : CochainComplex AddCommGrpCat.{u} ℕ}
    (iota : X ⟶ Y) (pi : Y ⟶ X) (hh : ∀ i, Y.X (i + 1) ⟶ Y.X i) (hretract : iota ≫ pi = 𝟙 X)
    (h0 : Y.d 0 (0 + 1) ≫ hh 0 + pi.f 0 ≫ iota.f 0 = 𝟙 (Y.X 0))
    (hsucc : ∀ i : ℕ, Y.d (i + 1) (i + 1 + 1) ≫ hh (i + 1) + hh i ≫ Y.d i (i + 1) +
      pi.f (i + 1) ≫ iota.f (i + 1) = 𝟙 (Y.X (i + 1))) :
    QuasiIso iota :=
  ⟨fun j => (quasiIsoAt_iff_isIso_homologyMap iota j).2
    (isIso_homologyMap_of_degreewiseHomotopyRetract iota pi hh hretract h0 hsucc j)⟩

end CompletedDeRham

/-! ### The row of a morphism -/

variable {K K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ}

/-- **The row `b` of a morphism of cochain complexes of cosimplicial abelian groups**: the family
of its components read in the simplex `⦋b⦌`.  `Crystalline.cosimplicialRowComplex` is the value of
a functor, and this is that functor on morphisms. -/
public def cosimplicialRowMap (rho : K ⟶ K') (b : ℕ) :
    cosimplicialRowComplex K b ⟶ cosimplicialRowComplex K' b :=
  ((alternatingCofaceMapComplex AddCommGrpCat.{u} ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) b).mapHomologicalComplex
      (ComplexShape.up ℕ)).map rho

/-- The exterior degree `a` of the row `b` of `rho` is its component `rho^a` read in the simplex
`⦋b⦌`. -/
public theorem cosimplicialRowMap_f (rho : K ⟶ K') (b a : ℕ) :
    (cosimplicialRowMap rho b).f a = (rho.f a).app ⦋b⦌ := rfl

/-- The row `b` of the identity is the identity. -/
public theorem cosimplicialRowMap_id
    (L : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ) (b : ℕ) :
    cosimplicialRowMap (𝟙 L) b = 𝟙 (cosimplicialRowComplex L b) :=
  ((alternatingCofaceMapComplex AddCommGrpCat.{u} ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) b).mapHomologicalComplex
      (ComplexShape.up ℕ)).map_id L

/-- The row `b` of a composite is the composite of the rows. -/
public theorem cosimplicialRowMap_comp
    {K'' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (rho : K ⟶ K')
    (rho' : K' ⟶ K'') (b : ℕ) :
    cosimplicialRowMap (rho ≫ rho') b =
      cosimplicialRowMap rho b ≫ cosimplicialRowMap rho' b :=
  ((alternatingCofaceMapComplex AddCommGrpCat.{u} ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) b).mapHomologicalComplex
      (ComplexShape.up ℕ)).map_comp rho rho'

/-! ### The two halves of the identification of the rows -/

/-- **The complex `Crystalline.cosimplicialDoubleComplexFunctor` extends once more**: the Moore
complex of `K` in each exterior degree, with the *inner* `ℕ`-to-`ℤ` extension performed and the
outer one still to come. -/
public abbrev cosimplicialDoubleComplexInner
    (L : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ) :
    CochainComplex (CochainComplex AddCommGrpCat.{u} ℤ) ℕ :=
  ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L)

/-- The morphism `Crystalline.cosimplicialDoubleComplexInner` carries a morphism of cochain
complexes of cosimplicial groups to. -/
public abbrev cosimplicialDoubleComplexInnerMap (rho : K ⟶ K') :
    cosimplicialDoubleComplexInner K ⟶ cosimplicialDoubleComplexInner K' :=
  ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map rho)

/-- **The outer half of `Crystalline.cosimplicialDoubleComplexRowIso`**: the outer `ℕ`-to-`ℤ`
extension commutes with reading the cosimplicial degree `b`, which is
`HomologicalComplex.mapHomologicalComplexExtendIso` at the degree-`b` evaluation functor. -/
public abbrev cosimplicialRowOuterIso
    (L : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ) (b : ℕ) :
    (((HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (b : ℤ)
          ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cosimplicialDoubleComplexInner L)).extend ComplexShape.embeddingUpNat ≅
      (cosimplicialDoubleComplexFunctor.obj L).flip.X (b : ℤ) :=
  HomologicalComplex.mapHomologicalComplexExtendIso
    (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (b : ℤ))
    (cosimplicialDoubleComplexInner L) ComplexShape.embeddingUpNat

/-- **The inner half of `Crystalline.cosimplicialDoubleComplexRowIso`**: reading the cosimplicial
degree `b` of the inner extension is reading the degree `b` of the Moore complex itself, which is
`ComplexShape.Embedding.extendFunctorCompEvalIso` applied degreewise. -/
public abbrev cosimplicialRowInnerIso
    (L : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ) (b : ℕ) :
    ((HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (b : ℤ)
          ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cosimplicialDoubleComplexInner L) ≅
      cosimplicialRowComplex L b :=
  (NatIso.mapHomologicalComplex
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{u}
      (show ComplexShape.embeddingUpNat.f b = (b : ℤ) from rfl))
    (ComplexShape.up ℕ)).app
      (((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L)

/-- **`Crystalline.cosimplicialDoubleComplexRowIso` is the composite of its two halves**, which is
how it is defined. -/
public theorem cosimplicialDoubleComplexRowIso_hom
    (L : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ) (b : ℕ) :
    (cosimplicialDoubleComplexRowIso L b).hom =
      (cosimplicialRowOuterIso L b).inv ≫
        HomologicalComplex.extendMap (cosimplicialRowInnerIso L b).hom
          ComplexShape.embeddingUpNat := rfl

/-- **A row of the flip of the double complex of `rho` is the degree-`b` evaluation of the outer
extension of `rho`**, which is how the double complex is built. -/
public theorem flipMap_cosimplicialDoubleComplexFunctor_map_f (rho : K ⟶ K') (b : ℕ) :
    (StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map rho)).f (b : ℤ) =
      ((HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (b : ℤ)
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap (cosimplicialDoubleComplexInnerMap rho)
          ComplexShape.embeddingUpNat) := rfl

/-! ### The identification of the rows is natural -/

/-- **`Crystalline.cosimplicialDoubleComplexRowIso` is natural in `K`.**

The row `b` of the flip of the double complex of `rho` corresponds, under the identification of
the rows of the double complex with the extensions of the rows of `K`, to the extension of the
row `b` of `rho`.

The identification is a composite of two isomorphisms and each is natural in the complex: the
outer extension is moved past the degree-`b` evaluation by
`HomologicalComplex.mapHomologicalComplexExtendIso`, whose naturality in the complex is
`HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality`, and the inner extension is
absorbed by a natural transformation applied degreewise, whose naturality is its own. -/
public theorem cosimplicialDoubleComplexRowIso_naturality (rho : K ⟶ K') (b : ℕ) :
    (StacksDraft.TotalRowComparison.flipMap
          (cosimplicialDoubleComplexFunctor.map rho)).f (b : ℤ) ≫
        (cosimplicialDoubleComplexRowIso K' b).hom =
      (cosimplicialDoubleComplexRowIso K b).hom ≫
        HomologicalComplex.extendMap (cosimplicialRowMap rho b) ComplexShape.embeddingUpNat := by
  have hnat := (NatIso.mapHomologicalComplex
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{u}
        (show ComplexShape.embeddingUpNat.f b = (b : ℤ) from rfl))
      (ComplexShape.up ℕ)).hom.naturality
    (((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map rho)
  have hext : (StacksDraft.TotalRowComparison.flipMap
          (cosimplicialDoubleComplexFunctor.map rho)).f (b : ℤ) ≫
        (cosimplicialRowOuterIso K' b).inv =
      (cosimplicialRowOuterIso K b).inv ≫
        HomologicalComplex.extendMap
          (((HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (b : ℤ)
              ).mapHomologicalComplex (ComplexShape.up ℕ)).map
            (cosimplicialDoubleComplexInnerMap rho)) ComplexShape.embeddingUpNat :=
    HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
      (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (b : ℤ))
      (cosimplicialDoubleComplexInner K) (cosimplicialDoubleComplexInnerMap rho)
      ComplexShape.embeddingUpNat
  rw [cosimplicialDoubleComplexRowIso_hom, cosimplicialDoubleComplexRowIso_hom,
    ← Category.assoc, hext, Category.assoc,
    Category.assoc, ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  exact congrArg (fun psi => (cosimplicialRowOuterIso K b).inv ≫
    HomologicalComplex.extendMap psi ComplexShape.embeddingUpNat) hnat

/-- **The square of `Crystalline.cosimplicialDoubleComplexRowIso_naturality` as an isomorphism of
arrows**, which is the shape `CategoryTheory.quasiIso_of_arrow_mk_iso` consumes. -/
public def cosimplicialDoubleComplexRowArrow (rho : K ⟶ K') (b : ℕ) :
    Arrow.mk (HomologicalComplex.extendMap (cosimplicialRowMap rho b)
        ComplexShape.embeddingUpNat) ≅
      Arrow.mk ((StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map rho)).f (b : ℤ)) :=
  Arrow.isoMk (cosimplicialDoubleComplexRowIso K b).symm
    (cosimplicialDoubleComplexRowIso K' b).symm
    (by
      dsimp only [Arrow.mk_hom, Iso.symm_hom]
      calc (cosimplicialDoubleComplexRowIso K b).inv ≫
              (StacksDraft.TotalRowComparison.flipMap
                (cosimplicialDoubleComplexFunctor.map rho)).f (b : ℤ)
          = (cosimplicialDoubleComplexRowIso K b).inv ≫
              ((StacksDraft.TotalRowComparison.flipMap
                  (cosimplicialDoubleComplexFunctor.map rho)).f (b : ℤ) ≫
                (cosimplicialDoubleComplexRowIso K' b).hom) ≫
              (cosimplicialDoubleComplexRowIso K' b).inv := by simp
        _ = (cosimplicialDoubleComplexRowIso K b).inv ≫
              ((cosimplicialDoubleComplexRowIso K b).hom ≫
                HomologicalComplex.extendMap (cosimplicialRowMap rho b)
                  ComplexShape.embeddingUpNat) ≫
              (cosimplicialDoubleComplexRowIso K' b).inv := by
              rw [cosimplicialDoubleComplexRowIso_naturality]
        _ = HomologicalComplex.extendMap (cosimplicialRowMap rho b)
              ComplexShape.embeddingUpNat ≫
            (cosimplicialDoubleComplexRowIso K' b).inv := by simp)

/-! ### The rowwise hypothesis -/

/-- **The rowwise hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] from the rows of `rho`.**

If the row `b` of `rho` is a quasi-isomorphism for every `b : ℕ` then every row map of the double
complex of `rho` is one — which is the hypothesis `hrows` of
`...SmallSite.computes07LG_of_doubleComplex`.  The rows indexed by a negative integer need no
hypothesis: both sides vanish there, by
`Crystalline.isZero_cosimplicialDoubleComplex_flip_X_X_of_neg`. -/
public theorem quasiIso_flipMap_of_quasiIso_row (rho : K ⟶ K')
    (h : ∀ b : ℕ, QuasiIso (cosimplicialRowMap rho b)) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) := by
  by_cases hb : 0 ≤ b
  · lift b to ℕ using hb
    have := h b
    have : QuasiIso (HomologicalComplex.extendMap (cosimplicialRowMap rho b)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff (cosimplicialRowMap rho b)
        ComplexShape.embeddingUpNat).2 (h b)
    exact quasiIso_of_arrow_mk_iso _ _ (cosimplicialDoubleComplexRowArrow rho b)
  · have h₁ : IsZero ((cosimplicialDoubleComplexFunctor.obj K).flip.X b) :=
      StacksDraft.TotalDegeneration.isZero_of_isZero_X
        (fun a => isZero_cosimplicialDoubleComplex_flip_X_X_of_neg K (by omega) a)
    have h₂ : IsZero ((cosimplicialDoubleComplexFunctor.obj K').flip.X b) :=
      StacksDraft.TotalDegeneration.isZero_of_isZero_X
        (fun a => isZero_cosimplicialDoubleComplex_flip_X_X_of_neg K' (by omega) a)
    have := StacksDraft.TotalComplexQuasiIso.isIso_of_isZero
      ((StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map rho)).f b) h₁ h₂
    infer_instance

/-- **The converse**: a row map of the double complex being a quasi-isomorphism makes the
corresponding row of `rho` one.

So the hypothesis of `Crystalline.quasiIso_flipMap_of_quasiIso_row` is not merely sufficient for
the rowwise hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] but equivalent to it, the rows
indexed by a negative integer carrying no information. -/
public theorem quasiIso_row_of_quasiIso_flipMap (rho : K ⟶ K') (b : ℕ)
    (h : QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f (b : ℤ))) :
    QuasiIso (cosimplicialRowMap rho b) := by
  have := h
  have : QuasiIso (HomologicalComplex.extendMap (cosimplicialRowMap rho b)
      ComplexShape.embeddingUpNat) :=
    quasiIso_of_arrow_mk_iso _ _ (cosimplicialDoubleComplexRowArrow rho b).symm
  exact (HomologicalComplex.quasiIso_extendMap_iff (cosimplicialRowMap rho b)
    ComplexShape.embeddingUpNat).1 this

/-- The rowwise hypothesis from sections of `rho` which are quasi-isomorphisms. -/
private theorem quasiIso_flipMap_of_quasiIso_section {R : CochainComplex AddCommGrpCat.{u} ℕ}
    (rho : K ⟶ constantCosimplicialCochainComplex.obj R)
    (iotaRow : ∀ b : ℕ, R ⟶ cosimplicialRowComplex K b) [∀ b, QuasiIso (iotaRow b)]
    (hsec : ∀ b : ℕ, iotaRow b ≫ cosimplicialRowMap rho b = 𝟙 R) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) :=
  quasiIso_flipMap_of_quasiIso_row rho
    (fun c => CompletedDeRham.quasiIso_of_section (iotaRow c) _ (hsec c)) b

/-- **The rowwise hypothesis from a homotopy equivalence of each row with `R`.**

Each row of `K` is compared with `R` by `rho`, and the hypothesis is that in each cosimplicial
degree `b` there is a section `iotaRow b` of that comparison which is a homotopy equivalence: a
retraction `piRow b` with `iotaRow b ≫ piRow b = 𝟙` and a chain homotopy from
`piRow b ≫ iotaRow b` to the identity.
That is exactly the data the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD]
produces, and `hsec` is the retraction property of the codiagonal. -/
public theorem quasiIso_flipMap_of_rowHomotopyEquiv {R : CochainComplex AddCommGrpCat.{u} ℕ}
    (rho : K ⟶ constantCosimplicialCochainComplex.obj R)
    (iotaRow : ∀ b : ℕ, R ⟶ cosimplicialRowComplex K b)
    (piRow : ∀ b : ℕ, cosimplicialRowComplex K b ⟶ R)
    (hretract : ∀ b : ℕ, iotaRow b ≫ piRow b = 𝟙 R)
    (hhomotopy : ∀ b : ℕ, _root_.Homotopy (piRow b ≫ iotaRow b) (𝟙 (cosimplicialRowComplex K b)))
    (hsec : ∀ b : ℕ, iotaRow b ≫ cosimplicialRowMap rho b = 𝟙 R) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) := by
  have (c : ℕ) : QuasiIso (iotaRow c) :=
    ⟨fun j => (quasiIsoAt_iff_isIso_homologyMap (iotaRow c) j).2
      (CompletedDeRham.isIso_homologyMap_of_homotopyRetract (iotaRow c) (piRow c) (hretract c)
        (hhomotopy c) j)⟩
  exact quasiIso_flipMap_of_quasiIso_section rho iotaRow hsec b

/-- **The rowwise hypothesis from a degreewise homotopy equivalence of each row with `R`**: the
shape `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` produces, with the chain homotopy
given as a degree-lowering family `hh` and the two contraction identities rather than as a
`Homotopy`. -/
public theorem quasiIso_flipMap_of_rowDegreewiseHomotopyEquiv
    {R : CochainComplex AddCommGrpCat.{u} ℕ}
    (rho : K ⟶ constantCosimplicialCochainComplex.obj R)
    (iotaRow : ∀ b : ℕ, R ⟶ cosimplicialRowComplex K b)
    (piRow : ∀ b : ℕ, cosimplicialRowComplex K b ⟶ R)
    (hh : ∀ (b : ℕ) (i : ℕ),
      (cosimplicialRowComplex K b).X (i + 1) ⟶ (cosimplicialRowComplex K b).X i)
    (hretract : ∀ b : ℕ, iotaRow b ≫ piRow b = 𝟙 R)
    (h0 : ∀ b : ℕ, (cosimplicialRowComplex K b).d 0 (0 + 1) ≫ hh b 0 +
      (piRow b).f 0 ≫ (iotaRow b).f 0 = 𝟙 ((cosimplicialRowComplex K b).X 0))
    (hsucc : ∀ (b : ℕ) (i : ℕ), (cosimplicialRowComplex K b).d (i + 1) (i + 1 + 1) ≫
        hh b (i + 1) + hh b i ≫ (cosimplicialRowComplex K b).d i (i + 1) +
        (piRow b).f (i + 1) ≫ (iotaRow b).f (i + 1) =
      𝟙 ((cosimplicialRowComplex K b).X (i + 1)))
    (hsec : ∀ b : ℕ, iotaRow b ≫ cosimplicialRowMap rho b = 𝟙 R) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) := by
  have (c : ℕ) : QuasiIso (iotaRow c) :=
    CompletedDeRham.quasiIso_of_degreewiseHomotopyRetract (iotaRow c) (piRow c) (hh c) (hretract c)
      (h0 c) (hsucc c)
  exact quasiIso_flipMap_of_quasiIso_section rho iotaRow hsec b

end Crystalline

end
