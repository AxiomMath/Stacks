module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackNatTransAlongAComposite

/-!
# The left comparison along a composite

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`Stacks.Cohomology.DerivedPullbackTensor.leftComparison` compares `Lf^*(QK ⊗^L_{𝒪_Y} QL)` with
`Q(f^*Tot(K ⊗_{𝒪_Y} L))`: it is the canonical map to the ordinary total tensor complex on `Y`,
followed by the comparison `Lf^*(QM) ⟶ Q(f^*M)`.  This file proves that the left comparison is
compatible with composition of morphisms of ringed spaces, and records the three auxiliary
identities in the shapes a chase of the *right* comparison consumes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.leftComparison_comp`: **the left comparison is
  compatible with composition.**  The composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of
  Stacks 0D5S carries the left comparison for `f ≫ g` to the derived pullback along `f` of the
  left comparison for `g`, followed by the comparison `Lf^*(Qg^*M) ⟶ Q(f^*g^*M)` and the
  composition law `f^*g^* ≅ (f ≫ g)^*` on complexes.  No K-flatness is needed: this is an
  identity between morphisms attached to arbitrary cochain complexes.
* `Stacks.Cohomology.DerivedPullbackTensor.leftComparison_app`: the left comparison at a pair of
  cochain complexes, written out as the derived pullback of the canonical map to the ordinary
  total tensor complex followed by the comparison of a complex.  This holds by definition.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans_naturality_prod` and
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_naturality`:
  naturality of the canonical map to the ordinary total tensor complex, and of Stacks 079U, at a
  *pair* of morphisms, written with the two one-sided actions spelled out rather than through
  `CategoryTheory.Functor.prod` and `CategoryTheory.Functor.comp`.
* Six abstract lemmas — `Stacks.Cohomology.DerivedPullbackTensor.comp_naturality_of_app`,
  `Stacks.Cohomology.DerivedPullbackTensor.comparison_comp_of_pieces`,
  `Stacks.Cohomology.DerivedPullbackTensor.map_right_comp`,
  `Stacks.Cohomology.DerivedPullbackTensor.right_comp_of_pieces`,
  `Stacks.Cohomology.DerivedPullbackTensor.comp_inv_eq_of_hom_comp` and
  `Stacks.Cohomology.DerivedPullbackTensor.comp_eq_map_comp` — which carry out, for arbitrary
  categories and functors, the diagram chases that a composition law for Stacks 079U is assembled
  from.

## Implementation notes

*Why the chases are abstract.*  The concrete functors here are derived functors on derived
categories of sheaves of modules.  Writing down a single composite of four morphisms between
objects built from total tensor complexes costs tens of thousands of heartbeats, almost all of it
in deciding definitional equality between the codomain of one factor and the domain of the next;
`rw` additionally has to abstract such a subterm into a rewrite motive, and the resulting motive
is not type-correct at `implicit` transparency.  Both problems disappear at the abstract
statements below, where every term is small, and the abstract lemmas are then applied by
unification through `exact`, never by rewriting.

*Bracketing is load-bearing.*  Composition in a category is associative only up to a
propositional equality, so each abstract hypothesis is stated at exactly the bracketing the
concrete terms carry.  A hypothesis written `p ≫ q ≫ r ≫ h` is not applicable to a goal
bracketed `(p ≫ q ≫ r) ≫ h`.

*What is not here: the right comparison along a composite, and so the composition law for Stacks
079U.*  The remaining step is a single identity — `Stacks 079U` for `f ≫ g`, followed by
`Stacks.Cohomology.DerivedPullbackTensor.rightComparison` for `f ≫ g`, equals the derived
pullback of the two factors, then the right comparison for `f`, then the comparison of total
complexes — together with the cancellation of the right comparison, which is invertible on
K-flat representatives.  `comparison_comp_of_pieces` performs that cancellation and the whole
assembly from six hypotheses, five of which are already available: the two instances of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_rightComparison`,
the invertibility of the right comparison, `leftComparison_comp`, and the combination of
`map_right_comp` with `comp_eq_map_comp` and
`derivedPullbackTensorIso_hom_app_naturality`.  The missing sixth is the composition law for the
right comparison, which `right_comp_of_pieces` reduces to the component of the right comparison
at a pair, naturality of the canonical map to the total tensor complex, the composition law for
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans`, and
`Stacks.PullbackTensorComposition.pullbackTensorComplexNatIso_comp` inverted by
`comp_inv_eq_of_hom_comp`.

That identity is mathematically complete and type-correct, and the assembly it feeds costs some
one hundred and forty thousand heartbeats — well inside the budget this library is held to.  What
does not fit is *writing the identity down*: elaborating its statement alone costs upwards of two
hundred thousand heartbeats, as does elaborating the statement of the component of the right
comparison at a pair.  Presenting the two bridging morphisms as separate definitions, so that
their types are read from the environment rather than re-elaborated, brings those statements down
to roughly one hundred and forty thousand — but then the definitions themselves cost four to
eight hundred thousand, because a definition with no ascribed type has to synthesise the type of
a composite of maps between total tensor complexes from scratch.  Each of these presentations
puts at least one declaration over the budget; the obstruction is localised to the
statement of that one identity rather than to the chase that consumes it.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

/-! ### The abstract chases -/

/-- **A resolution of an object, carried along a comparison of composite functors.**  Let
`c : Pg ⋙ Pf ⟶ Ph`, let `s : W ⟶ M`, and let `νg, νf, κ, νh` resolve `M` along `Pg`, then `Pf`,
and along `Ph`.  If the composition law `hc` holds at `M`, then it holds at `s`.

This is naturality of `c` at `s` followed by `hc`, and it is the step that carries a composition
law from an object to a map into that object. -/
theorem comp_naturality_of_app {CZ CY CX : Type*} [Category CZ] [Category CY]
    [Category CX] {Pg : CZ ⥤ CY} {Pf : CY ⥤ CX} {Ph : CZ ⥤ CX} (c : Pg ⋙ Pf ⟶ Ph)
    {W M : CZ} (s : W ⟶ M) {NY : CY} {NX NX' : CX}
    {νg : Pg.obj M ⟶ NY} {νf : Pf.obj NY ⟶ NX} {κ : NX ⟶ NX'} {νh : Ph.obj M ⟶ NX'}
    {lh : Ph.obj W ⟶ NX'} {lg : Pg.obj W ⟶ NY}
    (hlh : lh = Ph.map s ≫ νh) (hlg : lg = Pg.map s ≫ νg)
    (hc : c.app M ≫ νh = Pf.map νg ≫ νf ≫ κ) :
    c.app W ≫ lh = Pf.map lg ≫ νf ≫ κ := by
  rw [hlh, hlg, Pf.map_comp_assoc, ← hc, ← c.naturality_assoc]
  simp only [Functor.comp_map]

/-- **The assembly of a composition law for a comparison of a tensor product with the tensor
product of the images.**  Write `th` for the comparison at the composite and `tgA`, `tfA` for the
comparisons at the two factors, `rh` and `rfm` for the maps into the models, `lh` and `lg` for
the two comparisons they cancel against, and `qk`, `qc`, `nf` for the transports.  Given

* `hth`, `hg2`: the model identity at the composite and at the first factor;
* `hmono`: that the model map at the composite is a monomorphism;
* `hL`: the composition law for the other comparison;
* `hR`: the composition law for the model map;
* `hcomb`: the model identity at the second factor, transported,

the comparison at the composite is the two comparisons at the factors.  Both sides become maps
into the model after postcomposition with `rh`, which is a monomorphism, so the identity is
proved by cancelling it; after that `hth` and `hL` rewrite the left side and `hR`, `hg2` and
`hcomb` the right. -/
theorem comparison_comp_of_pieces {CY CX : Type*} [Category CY] [Category CX]
    (Pf : CY ⥤ CX)
    {Wg Eg Ng : CY} {P' MX NX FX FX' MY' GX : CX}
    {tgA : Wg ⟶ Eg} {rg : Eg ⟶ Ng} {lg : Wg ⟶ Ng}
    {c₀ : Pf.obj Wg ⟶ P'} {th : P' ⟶ GX} {lh : P' ⟶ MX}
    {nf : Pf.obj Ng ⟶ NX} {qk : NX ⟶ MX}
    {tfA : Pf.obj Eg ⟶ FX} {u : FX ⟶ FX'} {rfm : FX' ⟶ MY'} {qc : MY' ⟶ NX}
    {w : FX ⟶ GX} {rh : GX ⟶ MX}
    (hth : th ≫ rh = lh) (hmono : Mono rh)
    (hL : c₀ ≫ lh = Pf.map lg ≫ nf ≫ qk)
    (hR : w ≫ rh = u ≫ rfm ≫ qc ≫ qk)
    (hcomb : Pf.map rg ≫ nf = tfA ≫ u ≫ rfm ≫ qc)
    (hg2 : tgA ≫ rg = lg) :
    c₀ ≫ th = Pf.map tgA ≫ tfA ≫ w := by
  have := hmono
  apply (cancel_mono rh).1
  simp only [Category.assoc]
  rw [hth, hL, hR, ← hg2, Pf.map_comp_assoc, reassoc_of% hcomb]

/-- **The transported model identity that `comparison_comp_of_pieces` consumes as `hcomb`.**  The
image under `Pf` of a model map, followed by a transport, is the comparison at the second factor
followed by the model map there: naturality of the comparison (`hN`), the model identity at the
second factor (`hf3`) and the transport of the other comparison (`h8`). -/
theorem map_right_comp {CY CX : Type*} [Category CY] [Category CX] (Pf : CY ⥤ CX)
    {Eg Eg' Ng : CY} {FX FX' MY' NX : CX}
    {v : Eg ⟶ Eg'} {sq : Eg' ⟶ Ng} {nf : Pf.obj Ng ⟶ NX}
    {tfA : Pf.obj Eg ⟶ FX} {u : FX ⟶ FX'} {tfA' : Pf.obj Eg' ⟶ FX'}
    {rfm : FX' ⟶ MY'} {lf : Pf.obj Eg' ⟶ MY'} {qc : MY' ⟶ NX}
    (hN : tfA ≫ u = Pf.map v ≫ tfA') (hf3 : tfA' ≫ rfm = lf)
    (h8 : lf ≫ qc = Pf.map sq ≫ nf) :
    Pf.map (v ≫ sq) ≫ nf = tfA ≫ u ≫ rfm ≫ qc := by
  rw [reassoc_of% hN, reassoc_of% hf3, h8, Pf.map_comp_assoc]

/-- **The composition law for a model map, from the composition law in each tensor factor.**  The
model map `rh` at the composite is a tensor product of resolutions `nk, nl` followed by a
comparison `σh` and a transport `cxh` (`hrh`), and likewise `rfm` at the second factor (`hrf`).
If the resolutions obey the composition law in each factor (`hk`, `hl`), the comparisons are
natural (`hσ`) and the transports obey the composition law (`hcx`), then the tensor product of
the two comparisons of the factors carries `rh` to `rfm` followed by the transports.

The two factorwise laws are combined into one law for the tensor product by extensionality in the
product category, which is what lets `hσ` and `hcx` be applied to a single morphism. -/
theorem right_comp_of_pieces {D C : Type*} [Category D] [Category C]
    (T : D × D ⥤ D) (Qf : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D} {Tf Th Mf Mg Mh : C}
    {ck : A₀ ⟶ A₁} {nk : A₁ ⟶ A₄} {pk : A₀ ⟶ A₂} {qk : A₂ ⟶ A₃} {rk : A₃ ⟶ A₄}
    {cl : B₀ ⟶ B₁} {nl : B₁ ⟶ B₄} {pl : B₀ ⟶ B₂} {ql : B₂ ⟶ B₃} {rl : B₃ ⟶ B₄}
    {σh : T.obj (A₄, B₄) ⟶ Qf.obj Th} {σf : T.obj (A₃, B₃) ⟶ Qf.obj Tf}
    {cxh : Th ⟶ Mh} {cxf : Tf ⟶ Mf} {mbm : Tf ⟶ Th} {bg : Mf ⟶ Mg} {kt : Mg ⟶ Mh}
    {rh : T.obj (A₁, B₁) ⟶ Qf.obj Mh} {rfm : T.obj (A₂, B₂) ⟶ Qf.obj Mf}
    (hrh : rh = T.map (nk ×ₘ nl) ≫ σh ≫ Qf.map cxh)
    (hrf : rfm = T.map (qk ×ₘ ql) ≫ σf ≫ Qf.map cxf)
    (hk : ck ≫ nk = pk ≫ qk ≫ rk) (hl : cl ≫ nl = pl ≫ ql ≫ rl)
    (hσ : T.map (rk ×ₘ rl) ≫ σh = σf ≫ Qf.map mbm)
    (hcx : mbm ≫ cxh = cxf ≫ bg ≫ kt) :
    T.map (ck ×ₘ cl) ≫ rh = T.map (pk ×ₘ pl) ≫ rfm ≫ Qf.map bg ≫ Qf.map kt := by
  have hpair : (ck ×ₘ cl) ≫ (nk ×ₘ nl) = (pk ×ₘ pl) ≫ (qk ×ₘ ql) ≫ (rk ×ₘ rl) := by
    ext
    · exact hk
    · exact hl
  rw [hrh, hrf, ← T.map_comp_assoc, hpair]
  simp only [T.map_comp, Category.assoc]
  rw [reassoc_of% hσ, ← Qf.map_comp, hcx]
  simp only [Qf.map_comp]

/-- **A composition law between isomorphisms, read on the inverses.**  From
`e₁.hom ≫ e₂.hom ≫ m = d ≫ e₃.hom` one gets `m ≫ e₃.inv = e₂.inv ≫ e₁.inv ≫ d`.  This is the
form in which a composition law for a comparison of total complexes is consumed by
`right_comp_of_pieces`, whose transports are the inverses. -/
lemma comp_inv_eq_of_hom_comp {C : Type*} [Category C] {W₁ W₂ W₃ W₄ W₅ : C}
    (e₁ : W₁ ≅ W₂) (e₂ : W₂ ≅ W₃) (e₃ : W₄ ≅ W₅) (m : W₃ ⟶ W₅) (d : W₁ ⟶ W₄)
    (h : e₁.hom ≫ e₂.hom ≫ m = d ≫ e₃.hom) :
    m ≫ e₃.inv = e₂.inv ≫ e₁.inv ≫ d := by
  have hd : d = (e₁.hom ≫ e₂.hom ≫ m) ≫ e₃.inv := by
    rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **A comparison postcomposed with a transport, folded back under the functor.**  If
`lf = Pf.map σ ≫ nf₁` and `nf₁` is natural at `t` (`hnat`), then `lf` followed by the transport
is `Pf.map (σ ≫ t)` followed by the resolution at the new object.  This is the step that produces
the hypothesis `h8` of `map_right_comp`. -/
lemma comp_eq_map_comp {CY CX : Type*} [Category CY] [Category CX] (Pf : CY ⥤ CX)
    {E₁ E₂ E₃ : CY} {N₁ N₂ : CX} {lf : Pf.obj E₁ ⟶ N₁} {σ : E₁ ⟶ E₂}
    {nf₁ : Pf.obj E₂ ⟶ N₁} {r : N₁ ⟶ N₂} {t : E₂ ⟶ E₃} {nf₂ : Pf.obj E₃ ⟶ N₂}
    (hl : lf = Pf.map σ ≫ nf₁) (hnat : nf₁ ≫ r = Pf.map t ≫ nf₂) :
    lf ≫ r = Pf.map (σ ≫ t) ≫ nf₂ := by
  rw [hl, Category.assoc, hnat, Pf.map_comp, Category.assoc]

/-! ### The comparisons at a pair of cochain complexes -/

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

section OneSpace

variable (W : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Naturality of the canonical map to the ordinary total tensor complex at a pair of cochain
maps**, with the action of the derived tensor product on a pair spelled out through the two
one-sided actions and the total complex of a pair of maps spelled out directly.  This is the
`naturality` field of `Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans`; the
restatement exists so that it can be applied by unification against goals in which the functor
compositions have already been reduced. -/
theorem derivedToTensorNatTrans_naturality_prod
    {K K' L L' : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf)).map
        (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
      (derivedToTensorNatTrans W).app (K', L') =
      (derivedToTensorNatTrans W).app (K, L) ≫
        DerivedCategory.Q.map
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf)).map (a ×ₘ b)) :=
  (derivedToTensorNatTrans W).naturality (a ×ₘ b)

end OneSpace

section OneMorphism

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The left comparison at a pair of cochain complexes.**  It is the derived pullback along `f`
of the canonical map `QK ⊗^L_{𝒪_Y} QL ⟶ Q(Tot(K ⊗_{𝒪_Y} L))`, followed by the comparison
`Lf^*(QM) ⟶ Q(f^*M)` at the total tensor complex.  Both whiskerings contribute their component on
the nose, so this holds by definition; it is recorded so that the two factors can be reasoned
about separately without unfolding
`Stacks.Cohomology.DerivedPullbackTensor.leftComparison` inside a concrete goal. -/
theorem leftComparison_app
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (leftComparison f).app (K, L) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((derivedToTensorNatTrans Y).app (K, L)) ≫
        (derivedPullbackNatTrans f).app
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj (K, L)) :=
  rfl

/-- **Naturality of Stacks 079U at a pair of morphisms of `D(𝒪_Y)`**, with the actions of the two
bifunctors on a pair spelled out through the derived pullback and the two one-sided actions.  This
is the `naturality` field of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, read in the direction and at
the spelling a chase of the composition law consumes. -/
theorem derivedPullbackTensorIso_hom_app_naturality
    {U U' V V' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (p : U ⟶ U') (q : V ⟶ V') :
    (derivedPullbackTensorIso f).hom.app (U, V) ≫
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map p ×ₘ
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map q) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
            (p ×ₘ q)) ≫
        (derivedPullbackTensorIso f).hom.app (U', V') :=
  ((derivedPullbackTensorIso f).hom.naturality (p ×ₘ q)).symm

end OneMorphism

section Composite

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The left comparison is compatible with composition of morphisms of ringed spaces.**  For
composable morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` and arbitrary cochain complexes `K, L` of
`𝒪_Z`-modules, the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S, followed by
the left comparison for `f ≫ g`, is the derived pullback along `f` of the left comparison for `g`,
followed by the comparison `Lf^*(Q g^*M) ⟶ Q(f^*g^*M)` at the total tensor complex and the
composition law `f^*g^* ≅ (f ≫ g)^*` on complexes.

Both sides are the derived pullback of the canonical map to the ordinary total tensor complex on
`Z` followed by a resolution, so the identity is naturality of the composition isomorphism at
that canonical map followed by the composition law for
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at the total tensor
complex — which is exactly what `comp_naturality_of_app` assembles.  No
K-flatness hypothesis is needed. -/
/- No `stacks` attribute: Stacks 079U is covered, unclaused, by
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`
(`DerivedPullback/PullbackTensorComparison.lean:494`) and Stacks 0D5S by
`Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparisonCanonical`
(`DerivedPullback/CompositionUnconditional.lean:152`). This is a compatibility of two auxiliary
comparisons used in those constructions, not a further clause of either statement, so claiming
coverage here would contradict the bare attributes there. -/
theorem leftComparison_comp
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (leftComparison (f ≫ g)).app (K, L) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((leftComparison g).app (K, L)) ≫
        (derivedPullbackNatTrans f).app ((pullbackComplex g).obj
            ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (K, L))) ≫
          DerivedCategory.Q.map
            ((Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app
              ((totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (K, L))) :=
  comp_naturality_of_app
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
    ((derivedToTensorNatTrans Z).app (K, L))
    (leftComparison_app (f ≫ g) K L) (leftComparison_app g K L)
    (derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans f g
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (K, L)))

end Composite

end Stacks.Cohomology.DerivedPullbackTensor

end
