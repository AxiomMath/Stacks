module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiAssembly

/-!
# The descent of the transition of Stacks 023T, and the Zariski descent datum

`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/ZariskiAssembly.lean` reduces the
effectivity half of [Stacks, Tag 023T] to a single statement,
`AlgebraicGeometry.QuasicoherentDescentData.ZariskiTransitionOverAnyBase`: the existence, over an
arbitrary scheme `V` over the base `S`, of a morphism between the pullbacks of the two chosen
local solutions whose restriction to every scheme mapping to a member of the covering family `𝒰`
is the corresponding `…localTransition`.  Its uniqueness is already a theorem there
(`…transition_ext`), so what is missing is existence.

This file proves that existence, and hence
`AlgebraicGeometry.QuasicoherentDescentData.ZariskiDescentDatumOverAffineCover` with no
hypothesis at all.

The gluing is the fpqc sheaf condition for the presheaf of morphisms of quasi-coherent sheaves of
modules, `AlgebraicGeometry.isSheafFor_presheafHom_fpqc`, applied to the base change
`𝒰.pullback₁ q`, which is an fpqc covering of `V`: through
`CategoryTheory.Pseudofunctor.bijective_toDescentData_map_iff` that condition says exactly that a
morphism of the canonical descent data of two quasi-coherent sheaves of modules on `V` relative
to that covering comes from a morphism on `V`.  A morphism of canonical descent data is a family
of morphisms over the members of the covering satisfying one compatibility, and the family is
built from `…localTransition`, which is available over every member of the base change because
such a member maps to a member of `𝒰`; its compatibility is `…localTransition_eq`, the
independence of the local transition from the member it is read off.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.pullHom_pullModComp_hom` and
  `…pullHom_pullModComp_inv`: **the associativity coherence of the comparison isomorphisms of the
  pullback pseudofunctor**, in the `pullHom` spelling — restricting the comparison at a
  factorization `g ≫ p` along `d` gives the comparison at the factorization `(d ≫ g) ≫ p`.  This
  is the pseudofunctor pentagon, and it is what relates the two spellings of a morphism between
  twofold pullbacks.
* `AlgebraicGeometry.QuasicoherentDescentData.ofObjHom`: **a family of morphisms between the
  restrictions of two sheaves of modules is a morphism of their canonical descent data as soon as
  its members agree after restriction to a common test object**, which is the compatibility
  condition in the `pullHom` spelling.
* `AlgebraicGeometry.QuasicoherentDescentData.exists_map_eq_of_pullHom_compatible` and
  `…exists_pullHom_eq_of_compatible`: **morphisms of quasi-coherent sheaves of modules glue along
  an fpqc covering family**, in the two spellings the assembly needs.
* `AlgebraicGeometry.QuasicoherentDescentData.zariskiTransitionOverAnyBase`: **the descended
  transition exists**, which is the statement `ZariskiAssembly.lean` isolated.
* `AlgebraicGeometry.QuasicoherentDescentData.zariskiDescentDatumOverAffineCover`:
  **`…ZariskiDescentDatumOverAffineCover` holds unconditionally**, hence so does the effectivity
  half of [Stacks, Tag 023T] along the chain recorded in `ZariskiAssembly.lean`.

## Implementation notes

Everything is read in the `pullHom` spelling of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat` and, where descent data appear, at the
level of `CategoryTheory.Pseudofunctor.DescentData` for sheaves of modules carrying no
quasi-coherence datum.  The reason is the one recorded in `ZariskiDatumAssembly.lean`: the
predicate cutting out the quasi-coherent descent data mentions
`AlgebraicGeometry.Scheme.ringCatSheaf`, whose type is not type-correct at the `implicit`
transparency level, so that identifying a component of
`AlgebraicGeometry.canonicalDescentFunctor` with the corresponding component of
`CategoryTheory.Pseudofunctor.DescentData.ofObj` exhausts the heartbeat budget.  That is why the
gluing is taken from `AlgebraicGeometry.isSheafFor_presheafHom_fpqc` rather than from
`…nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage`: the former is a
statement about sheaves of modules with quasi-coherence as a *typeclass hypothesis*, so the
descent data occurring in its proof are the plain ones, and no such identification is needed.

**The coherence.**  A morphism `pullMod (𝒱.f i) A ⟶ pullMod (𝒱.f i) B` between the restrictions
of `A = p₁^* M₁` and `B = p₂^* M₂` is a *twofold* pullback on each side, whereas
`…localTransition` is a morphism between *single* pullbacks along the composites; the two are
exchanged by conjugating with `AlgebraicGeometry.pullModComp`, and the restriction of such a
conjugate along a further morphism is computed by `pullHom_pullModComp_conj`.  Its two
ingredients are the associativity coherences `pullHom_pullModComp_hom` and
`pullHom_pullModComp_inv`, which are the pseudofunctor pentagon
`CategoryTheory.Pseudofunctor.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight` read through
`CategoryTheory.Cat.Hom.toNatIso`; no sheaf-of-modules computation enters, because the identity
is one between 2-morphisms of `CategoryTheory.Cat` and is already available in that generality.

**Why the compatibility condition is the one stated.**  The condition
`CategoryTheory.Pseudofunctor.DescentData.Hom.comm` conjugates both of its sides by the
comparison isomorphisms of `CategoryTheory.Pseudofunctor.DescentData.ofObj`, and those cancel in
pairs; what remains is the equality of the restrictions of the two members of the family to a
common test object, with no comparison isomorphism in it.  That reduction is Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.subtypeCompatibleHomEquiv`, which identifies morphisms
of canonical descent data with compatible families of sections of
`CategoryTheory.Pseudofunctor.presheafHom`, whose restriction maps are `pullHom`; `ofObjHom` only
has to rewrite those restriction maps, which is `presheafHom_map_eq`.  Taking the two occurrences
of that definitional equality at once instead — which is what checking the compatibility
condition against the `pullHom` one directly amounts to — exhausts the heartbeat budget, whereas
each occurrence on its own is immediate.

No `stacks` attribute is placed: the clause of [Stacks, Tag 023T] that these results complete is
tagged on the main statement of the chain, not here.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
  Pseudofunctor.LocallyDiscreteOpToCat

universe v u

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

/-! ### The associativity coherence of the comparison isomorphisms -/

section Coherence

variable {Z Y Y' Y'' : Scheme.{u}}

/-- `AlgebraicGeometry.pullModComp`, in the spelling of the pseudofunctor's `mapComp'`: it is the
comparison 2-isomorphism of `AlgebraicGeometry.modulePullbackPseudofunctor` at the factorization,
evaluated at the sheaf of modules. -/
theorem pullModComp_hom_eq (p : Y ⟶ Z) (g : Y' ⟶ Y) (gp : Y' ⟶ Z) (h : g ≫ p = gp)
    (M : modulePullbackPseudofunctor.obj (.mk (op Z))) :
    (pullModComp g p gp h M).hom =
      (modulePullbackPseudofunctor.mapComp' p.op.toLoc g.op.toLoc gp.op.toLoc
        (by rw [← h]; cat_disch)).hom.toNatTrans.app M :=
  rfl

/-- **The associativity coherence of the comparison isomorphisms of the pullback pseudofunctor.**
Restricting along `d` the comparison between the pullback along `g ≫ p` and the pullback along
`g` of the pullback along `p` gives the comparison at the factorization `(d ≫ g) ≫ p`.

This is the pseudofunctor pentagon
`CategoryTheory.Pseudofunctor.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight`: the first factor
of `pullHom` and the comparison it transports are the two comparisons occurring on one side of
the pentagon, the comparison the statement produces is one of the two on the other side, and the
remaining one cancels against the third factor of `pullHom`.  Nothing about sheaves of modules is
used — the identity holds for every pseudofunctor to `CategoryTheory.Cat`. -/
theorem pullHom_pullModComp_hom (p : Y ⟶ Z) (g : Y' ⟶ Y) (gp : Y' ⟶ Z) (h : g ≫ p = gp)
    (M : modulePullbackPseudofunctor.obj (.mk (op Z))) (d : Y'' ⟶ Y') (dg : Y'' ⟶ Y)
    (dgp : Y'' ⟶ Z) (h₁ : d ≫ g = dg) (h₂ : d ≫ gp = dgp) (h₃ : dg ≫ p = dgp) :
    pullHom (pullModComp g p gp h M).hom d dgp dg h₂ h₁ = (pullModComp dg p dgp h₃ M).hom := by
  simp only [pullModComp_hom_eq]
  dsimp only [pullHom]
  rw [modulePullbackPseudofunctor.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    (f₀₁ := p.op.toLoc) (f₁₂ := g.op.toLoc) (f₂₃ := d.op.toLoc) (f₀₂ := gp.op.toLoc)
    (f₁₃ := dg.op.toLoc) (f := dgp.op.toLoc) (h₀₂ := by rw [← h]; cat_disch)
    (h₁₃ := by rw [← h₁]; cat_disch) (hf := by rw [← h₂]; cat_disch)]
  simp

/-- **The associativity coherence of the comparison isomorphisms, for the inverses**: the
restriction along `d` of the inverse comparison at the factorization `g ≫ p` is the inverse
comparison at the factorization `(d ≫ g) ≫ p`.

The restriction of the inverse is a right inverse of the restriction of the comparison, by
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp` and
`AlgebraicGeometry.pullHom_one`, and the latter is the comparison at the new factorization by
`pullHom_pullModComp_hom`. -/
theorem pullHom_pullModComp_inv (p : Y ⟶ Z) (g : Y' ⟶ Y) (gp : Y' ⟶ Z) (h : g ≫ p = gp)
    (M : modulePullbackPseudofunctor.obj (.mk (op Z))) (d : Y'' ⟶ Y') (dg : Y'' ⟶ Y)
    (dgp : Y'' ⟶ Z) (h₁ : d ≫ g = dg) (h₂ : d ≫ gp = dgp) (h₃ : dg ≫ p = dgp) :
    pullHom (pullModComp g p gp h M).inv d dg dgp h₁ h₂ = (pullModComp dg p dgp h₃ M).inv := by
  have key : pullHom (pullModComp g p gp h M).inv d dg dgp h₁ h₂ ≫
      (pullModComp dg p dgp h₃ M).hom = 𝟙 _ := by
    rw [← pullHom_pullModComp_hom p g gp h M d dg dgp h₁ h₂ h₃,
      ← pullHom_comp (pullModComp g p gp h M).inv (pullModComp g p gp h M).hom d dg dgp dg
        h₁ h₂ h₁, Iso.inv_hom_id]
    exact pullHom_one d dg h₁
  calc pullHom (pullModComp g p gp h M).inv d dg dgp h₁ h₂
      = (pullHom (pullModComp g p gp h M).inv d dg dgp h₁ h₂ ≫
          (pullModComp dg p dgp h₃ M).hom) ≫ (pullModComp dg p dgp h₃ M).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (pullModComp dg p dgp h₃ M).inv := by rw [key, Category.id_comp]

/-- **The restriction of a morphism between twofold pullbacks, read through the comparison
isomorphisms.**  A morphism between the pullbacks along `g` of `p₁^* M₁` and of `p₂^* M₂` is the
conjugate by the comparisons of a morphism between the pullbacks along the composites `g ≫ p₁`
and `g ≫ p₂`; restricting the conjugate along `d` gives the conjugate of the restriction, with
the comparisons taken at the new factorizations.

This is the form in which the candidate transitions of the Zariski descent datum are fed to the
descent of morphisms: they are morphisms between *single* pullbacks, while a descent datum asks
for morphisms between *twofold* ones. -/
theorem pullHom_pullModComp_conj {Z₁ Z₂ : Scheme.{u}}
    {M₁ : modulePullbackPseudofunctor.obj (.mk (op Z₁))}
    {M₂ : modulePullbackPseudofunctor.obj (.mk (op Z₂))} (p₁ : Y ⟶ Z₁) (p₂ : Y ⟶ Z₂)
    (g : Y' ⟶ Y) (gp₁ : Y' ⟶ Z₁) (gp₂ : Y' ⟶ Z₂) (e₁ : g ≫ p₁ = gp₁) (e₂ : g ≫ p₂ = gp₂)
    (φ : pullMod gp₁ M₁ ⟶ pullMod gp₂ M₂) (d : Y'' ⟶ Y') (y : Y'' ⟶ Y) (yp₁ : Y'' ⟶ Z₁)
    (yp₂ : Y'' ⟶ Z₂) (hd : d ≫ g = y) (k₁ : d ≫ gp₁ = yp₁) (k₂ : d ≫ gp₂ = yp₂)
    (f₁ : y ≫ p₁ = yp₁) (f₂ : y ≫ p₂ = yp₂) :
    pullHom ((pullModComp g p₁ gp₁ e₁ M₁).inv ≫ φ ≫ (pullModComp g p₂ gp₂ e₂ M₂).hom)
        d y y hd hd =
      (pullModComp y p₁ yp₁ f₁ M₁).inv ≫ pullHom φ d yp₁ yp₂ k₁ k₂ ≫
        (pullModComp y p₂ yp₂ f₂ M₂).hom := by
  rw [pullHom_comp (pullModComp g p₁ gp₁ e₁ M₁).inv (φ ≫ (pullModComp g p₂ gp₂ e₂ M₂).hom)
      d y yp₁ y hd k₁ hd,
    pullHom_comp φ (pullModComp g p₂ gp₂ e₂ M₂).hom d yp₁ yp₂ y k₁ k₂ hd,
    pullHom_pullModComp_inv p₁ g gp₁ e₁ M₁ d y yp₁ hd k₁ f₁,
    pullHom_pullModComp_hom p₂ g gp₂ e₂ M₂ d y yp₂ hd k₂ f₂]

end Coherence

/-! ### Gluing morphisms along an fpqc covering family -/

section Gluing

variable {V : Scheme.{u}} {𝒱 : PreZeroHypercover.{v} V}

/-- **The restriction maps of the presheaf of morphisms are `pullHom`.**  For a morphism `m` of
the category of schemes over `V` with target the object `p : Y ⟶ V`, the action of
`CategoryTheory.Pseudofunctor.presheafHom` on `m` sends a morphism `p^* A ⟶ p^* B` to its
restriction along the underlying morphism of `m`.

This is the definition of `CategoryTheory.Pseudofunctor.presheafHom`, stated so that it can be
rewritten with.  It has to be: identifying the compatibility condition of a family of sections of
that presheaf with the displayed condition on `pullHom` in one step is the same definitional
equality taken at both of its occurrences at once, and that exhausts the heartbeat budget, while
each occurrence separately is immediate. -/
theorem presheafHom_map_eq (A B : modulePullbackPseudofunctor.obj (.mk (op V)))
    {Y : Scheme.{u}} (p : Y ⟶ V) (Z : Over V) (m : Z ⟶ Over.mk p)
    (φ : pullMod p A ⟶ pullMod p B) :
    (modulePullbackPseudofunctor.presheafHom A B).map m.op φ =
      pullHom φ m.left Z.hom Z.hom (Over.w m) (Over.w m) :=
  rfl

/-- **A compatible family of morphisms between the restrictions of two sheaves of modules, as a
morphism of their canonical descent data.**

`CategoryTheory.Pseudofunctor.DescentData.subtypeCompatibleHomEquiv` identifies such morphisms
with the compatible families of sections of
`CategoryTheory.Pseudofunctor.presheafHom` over the members of the family, read as objects of the
category of schemes over the base; the restriction maps of that presheaf are `pullHom`, so its
compatibility condition is exactly the one stated here, and in particular no comparison
isomorphism of the pullback pseudofunctor occurs in it. -/
noncomputable def ofObjHom (A B : modulePullbackPseudofunctor.obj (.mk (op V)))
    (σ : ∀ i, pullMod (𝒱.f i) A ⟶ pullMod (𝒱.f i) B)
    (hσ : ∀ {Y : Scheme.{u}} (y : Y ⟶ V) (i₁ i₂ : 𝒱.I₀) (d₁ : Y ⟶ 𝒱.X i₁) (d₂ : Y ⟶ 𝒱.X i₂)
      (hd₁ : d₁ ≫ 𝒱.f i₁ = y) (hd₂ : d₂ ≫ 𝒱.f i₂ = y),
      pullHom (σ i₁) d₁ y y hd₁ hd₁ = pullHom (σ i₂) d₂ y y hd₂ hd₂) :
    (modulePullbackPseudofunctor.toDescentData 𝒱.f).obj A ⟶
      (modulePullbackPseudofunctor.toDescentData 𝒱.f).obj B :=
  Pseudofunctor.DescentData.subtypeCompatibleHomEquiv modulePullbackPseudofunctor 𝒱.f
    ⟨σ, fun i₁ i₂ Z d₁ d₂ _ ↦
      (presheafHom_map_eq A B (𝒱.f i₁) Z d₁ (σ i₁)).trans
        ((hσ Z.hom i₁ i₂ d₁.left d₂.left (Over.w d₁) (Over.w d₂)).trans
          (presheafHom_map_eq A B (𝒱.f i₂) Z d₂ (σ i₂)).symm)⟩

/-- The components of `ofObjHom` are the members of the family it is built from. -/
theorem ofObjHom_hom (A B : modulePullbackPseudofunctor.obj (.mk (op V)))
    (σ : ∀ i, pullMod (𝒱.f i) A ⟶ pullMod (𝒱.f i) B)
    (hσ : ∀ {Y : Scheme.{u}} (y : Y ⟶ V) (i₁ i₂ : 𝒱.I₀) (d₁ : Y ⟶ 𝒱.X i₁) (d₂ : Y ⟶ 𝒱.X i₂)
      (hd₁ : d₁ ≫ 𝒱.f i₁ = y) (hd₂ : d₂ ≫ 𝒱.f i₂ = y),
      pullHom (σ i₁) d₁ y y hd₁ hd₁ = pullHom (σ i₂) d₂ y y hd₂ hd₂) (i : 𝒱.I₀) :
    (ofObjHom A B σ hσ).hom i = σ i :=
  rfl

/-- **The descent of morphisms of quasi-coherent sheaves of modules along an fpqc covering
family**, in the form `CategoryTheory.Pseudofunctor.bijective_toDescentData_map_iff` gives it:
restriction to the canonical descent data relative to the family is a bijection on morphisms.

This is the fpqc sheaf condition `AlgebraicGeometry.isSheafFor_presheafHom_fpqc` for the presheaf
of morphisms, read through that equivalence. -/
theorem bijective_toDescentData_map_of_mem_fpqcPrecoverage (𝒱 : PreZeroHypercover.{v} V)
    (h𝒱 : 𝒱.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} V)
    (A B : modulePullbackPseudofunctor.obj (.mk (op V))) (hA : A.IsQuasicoherent)
    (hB : B.IsQuasicoherent) :
    Function.Bijective
      ((modulePullbackPseudofunctor.toDescentData 𝒱.f).map : (A ⟶ B) → _) :=
  have := hA
  have := hB
  (Pseudofunctor.bijective_toDescentData_map_iff
      (F := modulePullbackPseudofunctor) 𝒱.f A B).mpr
    (isSheafFor_presheafHom_fpqc (S := V) A B 𝒱.f h𝒱)

/-- **Morphisms of quasi-coherent sheaves of modules glue along an fpqc covering family.**  A
family of morphisms between the restrictions of two quasi-coherent sheaves of modules to the
members of an fpqc covering family, whose members agree after restriction to a common test
object, is the restriction of a morphism on the base.

The compatibility makes the family a morphism of the two canonical descent data, `ofObjHom`, and
`bijective_toDescentData_map_of_mem_fpqcPrecoverage` produces a morphism on the base restricting
to it. -/
theorem exists_map_eq_of_pullHom_compatible (𝒱 : PreZeroHypercover.{v} V)
    (h𝒱 : 𝒱.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} V)
    (A B : modulePullbackPseudofunctor.obj (.mk (op V))) (hA : A.IsQuasicoherent)
    (hB : B.IsQuasicoherent) (σ : ∀ i, pullMod (𝒱.f i) A ⟶ pullMod (𝒱.f i) B)
    (hσ : ∀ {Y : Scheme.{u}} (y : Y ⟶ V) (i₁ i₂ : 𝒱.I₀) (d₁ : Y ⟶ 𝒱.X i₁) (d₂ : Y ⟶ 𝒱.X i₂)
      (hd₁ : d₁ ≫ 𝒱.f i₁ = y) (hd₂ : d₂ ≫ 𝒱.f i₂ = y),
      pullHom (σ i₁) d₁ y y hd₁ hd₁ = pullHom (σ i₂) d₂ y y hd₂ hd₂) :
    ∃ τ : A ⟶ B, ∀ i,
      (modulePullbackPseudofunctor.map (𝒱.f i).op.toLoc).toFunctor.map τ = σ i := by
  obtain ⟨τ, hτ⟩ := (bijective_toDescentData_map_of_mem_fpqcPrecoverage 𝒱 h𝒱 A B hA hB).2
    (ofObjHom A B σ hσ)
  refine ⟨τ, fun i ↦ (congrArg
    (fun ρ : (modulePullbackPseudofunctor.toDescentData 𝒱.f).obj A ⟶
      (modulePullbackPseudofunctor.toDescentData 𝒱.f).obj B ↦ ρ.hom i) hτ).trans
    (ofObjHom_hom A B σ hσ i)⟩

/-- **Morphisms between pullbacks of quasi-coherent sheaves of modules glue along an fpqc
covering family**, in the `pullHom` spelling: a family of morphisms between the pullbacks along
the composites `𝒱.f i ≫ p₁` and `𝒱.f i ≫ p₂`, compatible after restriction to a common test
object, is the restriction of a morphism between the pullbacks along `p₁` and `p₂`.

This is `exists_map_eq_of_pullHom_compatible` with the family conjugated by the comparison
isomorphisms, so that the compatibility and the conclusion both read at the level of single
pullbacks; `pullHom_pullModComp_conj` transports the compatibility across the conjugation, and
the conjugating isomorphisms cancel from the conclusion. -/
theorem exists_pullHom_eq_of_compatible (𝒱 : PreZeroHypercover.{v} V)
    (h𝒱 : 𝒱.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} V) {Z₁ Z₂ : Scheme.{u}}
    {M₁ : modulePullbackPseudofunctor.obj (.mk (op Z₁))}
    {M₂ : modulePullbackPseudofunctor.obj (.mk (op Z₂))} (p₁ : V ⟶ Z₁) (p₂ : V ⟶ Z₂)
    (hM₁ : (pullMod p₁ M₁).IsQuasicoherent) (hM₂ : (pullMod p₂ M₂).IsQuasicoherent)
    (L : ∀ i : 𝒱.I₀, pullMod (𝒱.f i ≫ p₁) M₁ ⟶ pullMod (𝒱.f i ≫ p₂) M₂)
    (hL : ∀ {Y : Scheme.{u}} (y : Y ⟶ V) (i₁ i₂ : 𝒱.I₀) (d₁ : Y ⟶ 𝒱.X i₁) (d₂ : Y ⟶ 𝒱.X i₂)
      (hd₁ : d₁ ≫ 𝒱.f i₁ = y) (hd₂ : d₂ ≫ 𝒱.f i₂ = y),
      pullHom (L i₁) d₁ (y ≫ p₁) (y ≫ p₂) (by rw [← Category.assoc, hd₁])
          (by rw [← Category.assoc, hd₁]) =
        pullHom (L i₂) d₂ (y ≫ p₁) (y ≫ p₂) (by rw [← Category.assoc, hd₂])
          (by rw [← Category.assoc, hd₂])) :
    ∃ τ : pullMod p₁ M₁ ⟶ pullMod p₂ M₂, ∀ i : 𝒱.I₀,
      pullHom τ (𝒱.f i) (𝒱.f i ≫ p₁) (𝒱.f i ≫ p₂) rfl rfl = L i := by
  obtain ⟨τ, hτ⟩ := exists_map_eq_of_pullHom_compatible 𝒱 h𝒱 (pullMod p₁ M₁) (pullMod p₂ M₂)
    hM₁ hM₂
    (fun i ↦ (pullModComp (𝒱.f i) p₁ (𝒱.f i ≫ p₁) rfl M₁).inv ≫ L i ≫
      (pullModComp (𝒱.f i) p₂ (𝒱.f i ≫ p₂) rfl M₂).hom)
    (fun y i₁ i₂ d₁ d₂ hd₁ hd₂ ↦ by
      rw [pullHom_pullModComp_conj p₁ p₂ (𝒱.f i₁) (𝒱.f i₁ ≫ p₁) (𝒱.f i₁ ≫ p₂) rfl rfl (L i₁)
          d₁ y (y ≫ p₁) (y ≫ p₂) hd₁ (by rw [← Category.assoc, hd₁])
          (by rw [← Category.assoc, hd₁]) rfl rfl,
        pullHom_pullModComp_conj p₁ p₂ (𝒱.f i₂) (𝒱.f i₂ ≫ p₁) (𝒱.f i₂ ≫ p₂) rfl rfl (L i₂)
          d₂ y (y ≫ p₁) (y ≫ p₂) hd₂ (by rw [← Category.assoc, hd₂])
          (by rw [← Category.assoc, hd₂]) rfl rfl,
        hL y i₁ i₂ d₁ d₂ hd₁ hd₂])
  refine ⟨τ, fun i ↦ ?_⟩
  have h₁ : (modulePullbackPseudofunctor.map (𝒱.f i).op.toLoc).toFunctor.map τ =
      (pullModComp (𝒱.f i) p₁ (𝒱.f i ≫ p₁) rfl M₁).inv ≫ L i ≫
        (pullModComp (𝒱.f i) p₂ (𝒱.f i ≫ p₂) rfl M₂).hom := hτ i
  rw [map_eq_pullHom' τ (𝒱.f i) (𝒱.f i ≫ p₁) (𝒱.f i ≫ p₂) rfl rfl] at h₁
  simpa only [Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_right] using h₁

end Gluing

/-! ### The commutations over a member of the base change -/

section Commutations

variable {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)

/-- A morphism to an affine open of the base lying over `q` stays over `q` after composition with
a further morphism. -/
theorem comp_affineCover_f_eq (a : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g : V ⟶ S.affineCover.X a) (hg : g ≫ S.affineCover.f a = q) {Y : Scheme.{u}} (y : Y ⟶ V) :
    (y ≫ g) ≫ S.affineCover.f a = y ≫ q := by
  rw [Category.assoc, hg]

/-- **A morphism into the base change of `𝒰` lies over the base through the second projection
too**, the fibre-product square commuting. -/
theorem pullbackSnd_comp_base_eq {V : Scheme.{u}} (q : V ⟶ S) (i : 𝒰.I₀) {Y : Scheme.{u}}
    (d : Y ⟶ pullback q (𝒰.f i)) (y : Y ⟶ V) (hd : d ≫ pullback.fst q (𝒰.f i) = y) :
    (d ≫ pullback.snd q (𝒰.f i)) ≫ 𝒰.f i = y ≫ q := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hd]

/-- A morphism into the base change of `𝒰`, followed by the first projection and a further
morphism, is the composite of the induced morphism to the base with that morphism.  It is stated
separately because the index of the base change has to be typed as an index of `𝒰` for a rewrite
to be possible at all. -/
theorem comp_pullbackFst_comp_eq {V T : Scheme.{u}} (q : V ⟶ S) (i : 𝒰.I₀) (g : V ⟶ T)
    {Y : Scheme.{u}} (d : Y ⟶ pullback q (𝒰.f i)) (y : Y ⟶ V)
    (hd : d ≫ pullback.fst q (𝒰.f i) = y) :
    d ≫ pullback.fst q (𝒰.f i) ≫ g = y ≫ g := by
  rw [← Category.assoc, hd]

/-- **A member of the base change of `𝒰` maps compatibly to an affine open of the base and to a
member of `𝒰`**, which is what `…localTransition` asks for. -/
theorem pullbackFst_comp_eq (a : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g : V ⟶ S.affineCover.X a) (hg : g ≫ S.affineCover.f a = q) (i : 𝒰.I₀) :
    (pullback.fst q (𝒰.f i) ≫ g) ≫ S.affineCover.f a = pullback.snd q (𝒰.f i) ≫ 𝒰.f i := by
  rw [Category.assoc, hg]; exact pullback.condition

/-- **A scheme over a member of the base change of `𝒰` maps compatibly to an affine open of the
base and to a member of `𝒰`.**  This is `pullbackFst_comp_eq` read after a further morphism, and
it is the hypothesis the restricted local transition carries. -/
theorem comp_pullbackSnd_eq (a : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g : V ⟶ S.affineCover.X a) (hg : g ≫ S.affineCover.f a = q) (i : 𝒰.I₀) {Y : Scheme.{u}}
    (d : Y ⟶ pullback q (𝒰.f i)) (y : Y ⟶ V) (hd : d ≫ pullback.fst q (𝒰.f i) = y) :
    (y ≫ g) ≫ S.affineCover.f a = (d ≫ pullback.snd q (𝒰.f i)) ≫ 𝒰.f i :=
  (comp_affineCover_f_eq a q g hg y).trans (pullbackSnd_comp_base_eq 𝒰 q i d y hd).symm

end Commutations

/-! ### The descended transition -/

/-- **The descent of the transition along the base change of the covering family**, which is the
one statement `ZariskiAssembly.lean` isolated.

Over a scheme `V` over `S` the base change `𝒰.pullback₁ q` is an fpqc covering of `V`, and over
each of its members — which maps both to the affine open `U a` and to a member of `𝒰` — the local
transition `…localTransition` is available.  The family of those local transitions is compatible
after restriction to a common test object: restricting a local transition gives a local
transition by `…pullHom_localTransition`, and the result does not depend on the member of `𝒰` it
is read off by `…localTransition_eq`.  So the family glues, by
`exists_pullHom_eq_of_compatible`, and the glued morphism restricts to the prescribed local
transition over every scheme mapping to a member of `𝒰`: such a scheme factors through the
corresponding member of the base change, and `…pullHom_pullHom` turns the restriction to that
member into the restriction to it. -/
theorem zariskiTransitionOverAnyBase : ZariskiTransitionOverAnyBase.{v, u} := by
  intro S 𝒰 h𝒰 D a b V q g₁ g₂ hg₁ hg₂
  have key : ∀ (i : 𝒰.I₀) {W : Scheme.{u}} (d : W ⟶ pullback q (𝒰.f i)) (m₁ : W ⟶ _) (m₂ : W ⟶ _)
      (c : W ⟶ 𝒰.X i) (hk₁ : d ≫ pullback.fst q (𝒰.f i) ≫ g₁ = m₁)
      (hk₂ : d ≫ pullback.fst q (𝒰.f i) ≫ g₂ = m₂) (hc : d ≫ pullback.snd q (𝒰.f i) = c)
      (h₁ : m₁ ≫ S.affineCover.f a = c ≫ 𝒰.f i) (h₂ : m₂ ≫ S.affineCover.f b = c ≫ 𝒰.f i),
      pullHom (localTransition 𝒰 h𝒰 D a b (pullback.fst q (𝒰.f i) ≫ g₁)
          (pullback.fst q (𝒰.f i) ≫ g₂) i (pullback.snd q (𝒰.f i))
          (pullbackFst_comp_eq 𝒰 a q g₁ hg₁ i) (pullbackFst_comp_eq 𝒰 b q g₂ hg₂ i))
        d m₁ m₂ hk₁ hk₂ = localTransition 𝒰 h𝒰 D a b m₁ m₂ i c h₁ h₂ :=
    fun i _ d m₁ m₂ c hk₁ hk₂ hc h₁ h₂ ↦ pullHom_localTransition 𝒰 h𝒰 D a b _ _ i _ _ _ d m₁ m₂
      c hk₁ hk₂ hc h₁ h₂
  obtain ⟨τ, hτ⟩ := exists_pullHom_eq_of_compatible (𝒰.pullback₁ q)
    (mem_fpqcPrecoverage_pullback₁ 𝒰 h𝒰 q) g₁ g₂
    (isQuasicoherent_pullMod_affineOpenModule 𝒰 h𝒰 D a g₁)
    (isQuasicoherent_pullMod_affineOpenModule 𝒰 h𝒰 D b g₂)
    (fun i ↦ localTransition 𝒰 h𝒰 D a b (pullback.fst q (𝒰.f i) ≫ g₁)
      (pullback.fst q (𝒰.f i) ≫ g₂) i (pullback.snd q (𝒰.f i))
      (pullbackFst_comp_eq 𝒰 a q g₁ hg₁ i) (pullbackFst_comp_eq 𝒰 b q g₂ hg₂ i))
    (fun y i₁ i₂ d₁ d₂ hd₁ hd₂ ↦
      (key i₁ d₁ (y ≫ g₁) (y ≫ g₂) _ (comp_pullbackFst_comp_eq 𝒰 q i₁ g₁ d₁ y hd₁)
          (comp_pullbackFst_comp_eq 𝒰 q i₁ g₂ d₁ y hd₁) rfl
          (comp_pullbackSnd_eq 𝒰 a q g₁ hg₁ i₁ d₁ y hd₁)
          (comp_pullbackSnd_eq 𝒰 b q g₂ hg₂ i₁ d₁ y hd₁)).trans
        ((localTransition_eq 𝒰 h𝒰 D a b (y ≫ q) (y ≫ g₁) (y ≫ g₂)
              (comp_affineCover_f_eq a q g₁ hg₁ y) (comp_affineCover_f_eq b q g₂ hg₂ y)
              i₁ (d₁ ≫ pullback.snd q (𝒰.f i₁)) (pullbackSnd_comp_base_eq 𝒰 q i₁ d₁ y hd₁)
              i₂ (d₂ ≫ pullback.snd q (𝒰.f i₂)) (pullbackSnd_comp_base_eq 𝒰 q i₂ d₂ y hd₂)
              (comp_pullbackSnd_eq 𝒰 a q g₁ hg₁ i₁ d₁ y hd₁)
              (comp_pullbackSnd_eq 𝒰 b q g₂ hg₂ i₁ d₁ y hd₁)
              (comp_pullbackSnd_eq 𝒰 a q g₁ hg₁ i₂ d₂ y hd₂)
              (comp_pullbackSnd_eq 𝒰 b q g₂ hg₂ i₂ d₂ y hd₂)).trans
          (key i₂ d₂ (y ≫ g₁) (y ≫ g₂) _ (comp_pullbackFst_comp_eq 𝒰 q i₂ g₁ d₂ y hd₂)
              (comp_pullbackFst_comp_eq 𝒰 q i₂ g₂ d₂ y hd₂) rfl
              (comp_pullbackSnd_eq 𝒰 a q g₁ hg₁ i₂ d₂ y hd₂)
              (comp_pullbackSnd_eq 𝒰 b q g₂ hg₂ i₂ d₂ y hd₂)).symm))
  refine ⟨τ, fun {W} m i c m₁ m₂ hm₁ hm₂ h₁ h₂ ↦ ?_⟩
  have hmq : m ≫ q = c ≫ 𝒰.f i := by rw [← hg₁, ← Category.assoc, hm₁]; exact h₁
  have hlift₁ : pullback.lift m c hmq ≫ pullback.fst q (𝒰.f i) = m := pullback.lift_fst _ _ _
  have hk₁ : pullback.lift m c hmq ≫ pullback.fst q (𝒰.f i) ≫ g₁ = m₁ := by
    rw [← Category.assoc, hlift₁, hm₁]
  have hk₂ : pullback.lift m c hmq ≫ pullback.fst q (𝒰.f i) ≫ g₂ = m₂ := by
    rw [← Category.assoc, hlift₁, hm₂]
  calc pullHom τ m m₁ m₂ hm₁ hm₂
      = pullHom τ (pullback.lift m c hmq ≫ pullback.fst q (𝒰.f i)) m₁ m₂
          (by rw [hlift₁, hm₁]) (by rw [hlift₁, hm₂]) :=
        pullHom_congr_mor τ hlift₁.symm m₁ m₂ hm₁ hm₂ (by rw [hlift₁, hm₁]) (by rw [hlift₁, hm₂])
    _ = pullHom (pullHom τ (pullback.fst q (𝒰.f i)) (pullback.fst q (𝒰.f i) ≫ g₁)
          (pullback.fst q (𝒰.f i) ≫ g₂) rfl rfl) (pullback.lift m c hmq) m₁ m₂ hk₁ hk₂ :=
        (pullHom_pullHom τ (pullback.fst q (𝒰.f i)) (pullback.fst q (𝒰.f i) ≫ g₁)
          (pullback.fst q (𝒰.f i) ≫ g₂) (pullback.lift m c hmq) m₁ m₂ rfl rfl hk₁ hk₂).symm
    _ = localTransition 𝒰 h𝒰 D a b m₁ m₂ i c h₁ h₂ := by
        rw [show pullHom τ (pullback.fst q (𝒰.f i)) (pullback.fst q (𝒰.f i) ≫ g₁)
          (pullback.fst q (𝒰.f i) ≫ g₂) rfl rfl = _ from hτ i]
        exact key i _ m₁ m₂ c hk₁ hk₂ (pullback.lift_snd _ _ _) h₁ h₂

/-- **`…ZariskiDescentDatumOverAffineCover`, with no hypothesis.**  Every quasi-coherent descent
datum relative to an fpqc covering family of a scheme `S` is, after restriction to the
affine-open refinement, isomorphic to the restriction of a quasi-coherent descent datum on the
affine open covering of `S`.

This is `…zariskiDescentDatumOverAffineCover_of_transition` with its one hypothesis discharged by
`zariskiTransitionOverAnyBase`.  By `…zariskiDescentDatumOverAffineCover_iff` it is the
effectivity half of [Stacks, Tag 023T], and by
`…isEffective_fpqcPrecoverage_of_zariskiDatum` it yields that half directly. -/
theorem zariskiDescentDatumOverAffineCover : ZariskiDescentDatumOverAffineCover.{v, u} :=
  zariskiDescentDatumOverAffineCover_of_transition zariskiTransitionOverAnyBase

end QuasicoherentDescentData

end AlgebraicGeometry

end
