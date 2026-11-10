module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Abelian
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Problem Description

This is Lemma 18.42.1 (tag 093J) of the Stacks project, in the section "Constant
sheaves" of the chapter "Modules on Sites."

Throughout we fix a site `C`, i.e. a category equipped with a Grothendieck topology
`J`. We work with presheaves and sheaves on `C` valued in the category of abelian
groups `AddCommGrpCat`.

## Main Definition(s)

1. **Constant presheaf.** For an abelian group `E`, the constant presheaf with value
   `E` is the presheaf `(Functor.const Cᵒᵖ).obj E`, taking value `E` on every object
   `U` of `C` with all restriction maps equal to the identity. In Mathlib this is the
   presheaf given by the constant functor with value `E`.

2. **Sheafification.** The sheafification functor `presheafToSheaf J A` is the left
   adjoint to the inclusion of sheaves into presheaves (`sheafToPresheaf`). On
   `AddCommGrpCat`-valued (pre)sheaves it is the associated-sheaf functor. A basic
   property used here is that sheafification is exact: it is additive and preserves
   both kernels and cokernels.

3. **Constant sheaf.** For an abelian group `E`, the constant sheaf `E` with value `E`
   is the sheafification of the constant presheaf. In Mathlib this is
   `(constantSheaf J A).obj E`, and by definition
   `constantSheaf J A = Functor.const Cᵒᵖ ⋙ presheafToSheaf J A`, i.e. exactly the
   sheafification of the constant presheaf. The assignment is functorial: a homomorphism
   `f : A ⟶ B` of abelian groups induces a morphism of constant presheaves and hence,
   by applying sheafification, a morphism of constant sheaves
   `(constantSheaf J _).map f`.

4. **Exactness of a sequence of abelian presheaves.** A sequence of abelian presheaves
   is exact if for every object `U` of `C` the induced sequence of abelian groups on
   sections over `U` is exact. We model a sequence `0 → F' → F → F'' → 0` by a
   `ShortComplex` and its `ShortExact` predicate, applied objectwise via the sections
   functor `(sheafSections J A).obj (op U)`.

5. **Exactness of a sequence of abelian sheaves.** A sequence `0 → F' → F → F'' → 0`
   of abelian sheaves is exact if it is exact (short exact) in the abelian category
   `Sheaf J AddCommGrpCat`. We model this by `ShortComplex.ShortExact`.

## Main Statement(s)

Let `C` be a site and let `0 → A → B → C → 0` (encoded by a short complex `S` with
`S.ShortExact`) be a short exact sequence of abelian groups. Applying the constant
sheaf functor `constantSheaf J AddCommGrpCat` produces a short complex of abelian
sheaves `S.map (constantSheaf J AddCommGrpCat)`. Then:

1. This sequence of constant sheaves is a short exact sequence of abelian sheaves.

2. This sequence is also exact as a sequence of abelian presheaves: for every object
   `U` of `C`, the sequence of abelian groups on sections over `U` is short exact. In
   particular the map `B → C` of constant sheaves is objectwise surjective on sections.
-/

open CategoryTheory Opposite

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

-- Main Definition(s)

/-- The constant presheaf of abelian groups with value `E`: the presheaf given by the
constant functor on `Cᵒᵖ`, taking value `E` on every object and the identity on every
restriction map. (Definition 1.) -/
@[ega "0 3.6.1"]
noncomputable def constantAbPresheaf (E : AddCommGrpCat.{u}) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const Cᵒᵖ).obj E

/-- The constant sheaf functor `constantSheaf J AddCommGrpCat` is, by definition, the
constant-presheaf functor followed by sheafification, matching Definition 3 (the
constant sheaf is the sheafification of the constant presheaf). This correctness
statement records that alignment. -/
theorem constantSheaf_eq_const_comp_sheafify :
    constantSheaf J AddCommGrpCat.{u}
      = (Functor.const Cᵒᵖ) ⋙ presheafToSheaf J AddCommGrpCat.{u} := rfl

/-- The constant presheaf agrees objectwise with the constant functor: its value on
every object `U` is `E`. This records that `constantAbPresheaf` matches Definition 1. -/
theorem constantAbPresheaf_obj (E : AddCommGrpCat.{u}) (U : Cᵒᵖ) :
    (constantAbPresheaf (C := C) E).obj U = E := rfl

-- Auxiliary: clean (proof-complete) finite-colimit preservation of sheafification.

/-- Sheafification `presheafToSheaf J AddCommGrpCat` preserves finite colimits, proved the
honest way: it is the left adjoint of `sheafToPresheaf` (`sheafificationAdjunction`), and a
left adjoint preserves all colimits. This avoids the environment's unproved exactness
instance (`CategoryTheory.presheafToSheaf_preservesFiniteColimits`), which `infer_instance` would
otherwise silently select. -/
theorem presheafToSheaf_preservesColimitsOfShape (K : Type) [SmallCategory K] :
    Limits.PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{u}) := by
  have hps : Limits.PreservesColimitsOfSize.{0, 0} (presheafToSheaf J AddCommGrpCat.{u}) :=
    (sheafificationAdjunction J AddCommGrpCat.{u}).leftAdjoint_preservesColimits
  exact hps.preservesColimitsOfShape

/-- `constantSheaf = const ⋙ presheafToSheaf` (by `rfl`) preserves finite colimits.
Both factors do — `const` trivially, and `presheafToSheaf` as a left adjoint
(see `presheafToSheaf_preservesColimitsOfShape`) — and we feed those clean instances
explicitly so that the composite avoids the unproved environment instance. -/
theorem constantSheaf_preservesColimitsOfShape (K : Type) [SmallCategory K] :
    Limits.PreservesColimitsOfShape K
      (Functor.const Cᵒᵖ ⋙ presheafToSheaf J AddCommGrpCat.{u}) := by
  have hpsK : Limits.PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{u}) :=
    presheafToSheaf_preservesColimitsOfShape J K
  have hconst : Limits.PreservesColimitsOfShape K
      (Functor.const Cᵒᵖ (C := AddCommGrpCat.{u})) := inferInstance
  exact @Limits.comp_preservesColimitsOfShape _ _ _ _ K _ _ _ _ _ hconst hpsK

/-- `constantSheaf J AddCommGrpCat` preserves finite colimits, with no open goals
(`#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`). Uses the defeq
`constantSheaf = const ⋙ presheafToSheaf` and the clean left-adjoint colimit preservation. -/
theorem constantSheaf_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (constantSheaf J AddCommGrpCat.{u}) :=
  ⟨fun K _ _ => constantSheaf_preservesColimitsOfShape J K⟩

/-- **`constantSheaf J AddCommGrpCat` preserves finite limits**, by the same defeq
`constantSheaf = const ⋙ presheafToSheaf` as its colimit companion: the constant-presheaf functor
preserves all limits, and sheafification preserves finite ones.

Together with `constantSheaf_preservesFiniteColimits` this says the constant sheaf functor is
**exact**, which is what promotes it to derived categories through
`CategoryTheory.Functor.mapDerivedCategory`. Since it is the left adjoint of global sections
(Mathlib's `CategoryTheory.constantSheafAdj`, whose right adjoint at the terminal open is
`Stacks.Cohomology.Leray.sectionsFunctor X ⊤`) and is also monoidal
(`Stacks.Cohomology.Leray.constantSheafMonoidal`), this is the premise of the adjoint route to a
*lax monoidal* `RΓ` — which is what a cup product on hypercohomology needs, and which
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal` delivers once the adjunction is available on
derived categories.

The statement was recorded as unavailable by the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafMonoidal.lean`, which asserts the exactness in
prose without a declaration, and by that of
`StacksFrontier/AlgebraicGeometry/DeRham/FirstChernClass/FilteredChernCupProduct.lean`, which called
it an instance that "has no instance" — while its proof sat inside the proof of
`constantSheaf_shortExact_of_shortExact` below.

Stated as a `theorem` rather than an `instance`, matching its colimit companion: consumers seat it
with `letI` or `attribute [local instance]`, `CategoryTheory.Limits.comp_preservesFiniteLimits`
being itself not an instance. -/
theorem constantSheaf_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{u}) := by
  have hconstPL : Limits.PreservesFiniteLimits
      (Functor.const Cᵒᵖ (C := AddCommGrpCat.{u})) := by
    refine ⟨fun K _ _ => ?_⟩
    exact Limits.PreservesLimitsOfSize.preservesLimitsOfShape
  have hsheafPL : Limits.PreservesFiniteLimits (presheafToSheaf J AddCommGrpCat.{u}) :=
    inferInstance
  rw [constantSheaf_eq_const_comp_sheafify]
  exact Limits.comp_preservesFiniteLimits _ _

-- Main Statement(s)

/-- **(1) Exactness as abelian sheaves.**

Given a short exact sequence `0 → A → B → C → 0` of abelian groups (a short complex `S`
with `S.ShortExact`), applying the constant sheaf functor yields a short exact sequence
of abelian sheaves `0 → A → B → C → 0` on the site `C`. -/
@[stacks 093J, ega "0 12.1.3" "special case", ega "IV 10.2.8" "special case"]
theorem constantSheaf_shortExact_of_shortExact
    (S : ShortComplex AddCommGrpCat.{u}) (hS : S.ShortExact) :
    (S.map (constantSheaf J AddCommGrpCat.{u})).ShortExact := by
  have := constantSheaf_preservesFiniteLimits J
  -- Use the clean (proof-complete) finite-colimit preservation, NOT `infer_instance` (which
  -- would pick the environment's unproved `CategoryTheory` instance).
  have : Limits.PreservesFiniteColimits (constantSheaf J AddCommGrpCat.{u}) :=
    constantSheaf_preservesFiniteColimits J
  have := hS.mono_f
  have := hS.epi_g
  have : Mono ((constantSheaf J AddCommGrpCat.{u}).map S.f) := by
    apply Functor.map_mono
  have : Epi ((constantSheaf J AddCommGrpCat.{u}).map S.g) := by
    apply Functor.map_epi
  exact hS.map _

/-- **Crux of part (2): objectwise surjectivity of `g` on sections.**

Given a short exact sequence `0 → A → B → C → 0` of abelian groups (`S.ShortExact`), the
induced map of constant sheaves `B̲ → C̲`, evaluated on sections over any object `U`, is
an epimorphism `B̲(U) → C̲(U)`. Equivalently (since `AddCommGrpCat` is concrete and
`epi_iff_surjective`) the function `B̲(U) → C̲(U)` is surjective.

This is THE nontrivial content of Stacks 093J: a short exact sequence of *sheaves* is in
general only LEFT exact on sections (the sections-over-`U` functor `F ↦ F(U)` preserves
finite limits but NOT finite colimits in general), so surjectivity on sections does not
follow formally from sheaf-level epimorphism. It holds here for the special reason that
`g : B → C` admits a set-theoretic right inverse.

RIGOROUS INFORMAL ARGUMENT (Stacks tag 093J).
Since `g : B → C` is surjective (from `hS.epi_g` via `AddCommGrpCat.epi_iff_surjective`),
choose a set-theoretic section `s : C → B` with `g ∘ s = id_C` (e.g. `Function.surjInv`;
`s` need NOT be a group homomorphism, and we never require it to be). This `s` is a
morphism of the underlying SETS, hence induces a morphism of constant *presheaves of sets*
`s̲ᵖ : C̲ᵖ → B̲ᵖ` (the identity `s` on every object), and after sheafification a morphism of
constant *sheaves of sets* `s̲ : C̲ → B̲`. Because `g ∘ s = id_C` as set maps, the induced
`g̲ ∘ s̲ = id` as a map of constant sheaves of sets (sheafification is a functor and the
relation `gᵖ ∘ sᵖ = id` holds objectwise on the constant presheaves). Evaluating at any
object `U` gives `g̲_U ∘ s̲_U = id` on the sets `C̲(U)`, so `s̲_U : C̲(U) → B̲(U)` is a
right inverse (a set-theoretic section) of `g̲_U : B̲(U) → C̲(U)`. A function with a right
inverse is surjective, so `g̲_U` is surjective, hence an epimorphism in `AddCommGrpCat`.

FORMALIZATION STRATEGY (for the formal phase).
The cleanest Mathlib route reduces the goal to a statement about the underlying sets:
  1. `rw [AddCommGrpCat.epi_iff_surjective]` (or `ConcreteCategory.epi_iff_surjective`) to
     turn the goal into `Function.Surjective` of the section map `B̲(U) → C̲(U)`.
  2. Obtain the set section `s := Function.surjInv hg` where `hg : Function.Surjective S.g`
     comes from `hS.epi_g` and `AddCommGrpCat.epi_iff_surjective`. Note `s` lives in `Set`,
     not in `AddCommGrpCat`, so the constant-sheaf-of-sets machinery is needed.
  3. Transport `s` through the constant-sheaf-of-SETS functor
     `constantSheaf J (Type u)` (or via `sheafCompose`/`forget`), using
     `constantCommuteCompose : constantSheaf J D ⋙ sheafCompose J U ≅ U ⋙ constantSheaf J B`
     to relate the `AddCommGrpCat`-valued and `Type`-valued constant sheaves, so that the
     section `s̲` of sets is a genuine right inverse of `g̲` on `U`-sections.
  4. Conclude surjectivity of `g̲_U` from `Function.RightInverse … → Surjective`.
ALTERNATIVE (heavier-machinery) route: the section-level functor
`constantSheaf J _ ⋙ (sheafSections J _).obj (op U) = constantSheaf ⋙ sheafToPresheaf ⋙
evaluation` preserves finite colimits (hence epis) — but the colimit-preservation of
`sheafToPresheaf J AddCommGrpCat` is the exactness-of-the-inclusion fact, which in the
current environment is itself an unproved instance; so the honest route is the
set-section argument above, not `ShortComplex.ShortExact.map_of_exact`.

SANITY CHECK PASSED (lean-sanity-check confirmed the statement is TRUE: it reduces by
`rfl`/`epi_iff_surjective` exactly to surjectivity of `B̲(U) → C̲(U)`, and the set-section
right-inverse argument is valid in every Grothendieck topos; degenerate topologies and
zero-section edge cases are vacuous or trivially true). -/
theorem constantSheaf_section_g_epi
    (S : ShortComplex AddCommGrpCat.{u}) (hS : S.ShortExact) (U : C) :
    Epi ((constantSheaf J AddCommGrpCat.{u}
        ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op U)).map S.g) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  set fgt := CategoryTheory.forget AddCommGrpCat.{u} with hfgt
  set Φ := constantSheaf J AddCommGrpCat.{u} ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op U) with
      hΦ
  set Ψ := constantSheaf J (Type u) ⋙ (sheafSections J (Type u)).obj (op U) with hΨ
  -- Key natural iso, built from `constantCommuteCompose` for the forgetful functor and the
  -- (definitional) commutation of `sheafCompose`/`sheafSections`: `Φ ⋙ fgt ≅ fgt ⋙ Ψ`.
  have key : Φ ⋙ fgt ≅ fgt ⋙ Ψ :=
    eqToIso (by rfl) ≪≫
      Functor.isoWhiskerRight (constantCommuteCompose J fgt) ((sheafSections J (Type u)).obj (op U))
  -- `g : B → C` is surjective on underlying sets, hence a split epi in `Type u`.
  have := hS.epi_g
  have hg : Function.Surjective (fgt.map S.g) := by
    rw [hfgt]; exact (AddCommGrpCat.epi_iff_surjective S.g).mp hS.epi_g
  have hsplit : IsSplitEpi (fgt.map S.g) := (isSplitEpi_iff_surjective _).mpr hg
  -- A functor preserves split epis, so `(fgt ⋙ Ψ).map S.g = Ψ.map (fgt.map S.g)` is a split epi.
  have hsplit2 : IsSplitEpi ((fgt ⋙ Ψ).map S.g) := by
    change IsSplitEpi (Ψ.map (fgt.map S.g)); infer_instance
  -- Transfer the split epi across the natural iso `key`.
  have hnat : (Φ ⋙ fgt).map S.g
      = key.hom.app S.X₂ ≫ (fgt ⋙ Ψ).map S.g ≫ key.inv.app S.X₃ := by
    have hn := key.hom.naturality S.g
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have : IsSplitEpi ((Φ ⋙ fgt).map S.g) := by
    rw [hnat]; infer_instance
  -- A split epi in `Type u` is surjective; this is exactly the goal for `Φ.map S.g`.
  exact (isSplitEpi_iff_surjective _).mp this

/-- **(2) Exactness as abelian presheaves.**

The same induced sequence of constant sheaves is exact as a sequence of abelian
presheaves: for every object `U` of `C`, the sequence of abelian groups obtained by
taking sections over `U` is short exact. In particular `B → C` is objectwise surjective
on sections. -/
@[stacks 093J]
theorem constantSheaf_sections_shortExact_of_shortExact
    (S : ShortComplex AddCommGrpCat.{u}) (hS : S.ShortExact) (U : C) :
    ((S.map (constantSheaf J AddCommGrpCat.{u})).map
        ((sheafSections J AddCommGrpCat.{u}).obj (op U))).ShortExact := by
  -- Strategy: take the sheaf-level short exact sequence from part (1) and apply the
  -- sections-over-`U` functor `G`. `G` preserves finite limits (clean, no open goals), which
  -- gives `Mono (G.map T.f)` (left exactness) and, via kernel forks, exactness at the
  -- middle of `T.map G`; the right-hand epimorphism `Epi (G.map T.g)` is exactly the crux
  -- `constantSheaf_section_g_epi`. We deliberately AVOID `map_of_exact`/`PreservesHomology`/
  -- `PreservesFiniteColimits` of `G`, which in this environment route through the
  -- unproved `CategoryTheory` colimit instance for `sheafToPresheaf`.
  set T := S.map (constantSheaf J AddCommGrpCat.{u}) with hT
  set G := (sheafSections J AddCommGrpCat.{u}).obj (op U) with hG
  -- Part (1): `T` is short exact as a sequence of abelian sheaves.
  have hTse : T.ShortExact := constantSheaf_shortExact_of_shortExact J S hS
  -- `G` preserves finite limits (`sheafSections = sheafToPresheaf ⋙ evaluation`, both clean).
  -- IMPORTANT: this is the clean route; we never use `PreservesFiniteColimits`/`PreservesHomology`
  -- of `G` (which would route through the unproved `CategoryTheory` instance for
  -- `sheafToPresheaf`). Instead, exactness at the middle is obtained from the fact that a
  -- finite-limit-preserving functor sends the kernel fork of `T.g` (with cone point `T.X₁`,
  -- which `T` short exact makes a limit) to a limit kernel fork.
  have hsec : (sheafSections J AddCommGrpCat.{u}).obj (op U)
      = sheafToPresheaf J AddCommGrpCat.{u}
          ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) := rfl
  have hpl : Limits.PreservesFiniteLimits G := by rw [hG, hsec]; infer_instance
  have := hTse.mono_f
  -- Supply a CLEAN `PreservesMonomorphisms G` from finite-limit preservation. The bare
  -- `infer_instance`/`G.map_mono` path would instead pick an unproved
  -- `PreservesMonomorphisms` instance specialized to the concrete section functor.
  have hpm : G.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape G
  have hmono : Mono (T.map G).f := by
    change Mono (G.map T.f); exact G.map_mono T.f
  have hepi : Epi (T.map G).g := by
    change Epi (G.map T.g); exact constantSheaf_section_g_epi J S hS U
  have hexact : (T.map G).Exact := by
    have hker : Limits.IsLimit (Limits.KernelFork.ofι T.f T.zero) := hTse.fIsKernel
    have hmap := Limits.KernelFork.mapIsLimit (Limits.KernelFork.ofι T.f T.zero) hker G
    refine ShortComplex.exact_of_f_is_kernel (T.map G) ?_
    exact Limits.IsLimit.ofIsoLimit hmap (hmap.uniqueUpToIso hmap)
  exact ShortComplex.ShortExact.mk hexact
