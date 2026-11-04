module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.RingedSpace.OpenImmersion
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
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks project Tag 01C8 (Lemma 17.14.3): the pullback of a locally free module
along a morphism of ringed spaces is locally free.

A ringed space is a pair $(X, \mathcal{O}_X)$ of a topological space $X$ together with
a sheaf of commutative unital rings $\mathcal{O}_X$ on $X$. A morphism of ringed spaces
$(f, f^\sharp) : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)$ is a continuous map
$f : X \to Y$ together with a map of sheaves of rings
$f^\sharp : \mathcal{O}_Y \to f_* \mathcal{O}_X$.

Definition 1 (Locally free, Tag 01C6): a sheaf of $\mathcal{O}_X$-modules $\mathcal{F}$
is locally free if for every $x \in X$ there are an index set $I$ and an open
neighbourhood $x \in U$ such that $\mathcal{F}|_U \cong \bigoplus_{i \in I}
(\mathcal{O}_X|_U)$ as $\mathcal{O}_X|_U$-modules. The set $I$ is arbitrary (possibly
infinite) and may depend on $x$; no constraint on rank is imposed (stalks of the
structure sheaf are permitted to be the zero ring).

Definition 2 (Pullback, Tag 01BG / Section 17.13): for a morphism of ringed spaces
$f$ and a sheaf of $\mathcal{O}_Y$-modules $\mathcal{G}$, the pullback is
$f^* \mathcal{G} = f^{-1}\mathcal{G} \otimes_{f^{-1}\mathcal{O}_Y} \mathcal{O}_X$;
it is the left adjoint of the pushforward $f_*$.

Statement 1 (Tag 01C8): if $f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)$ is a
morphism of ringed spaces and $\mathcal{G}$ is a locally free $\mathcal{O}_Y$-module,
then $f^* \mathcal{G}$ is a locally free $\mathcal{O}_X$-module.
-/

-- We work with Mathlib's `AlgebraicGeometry.RingedSpace`, which is by definition
-- `SheafedSpace CommRingCat`: a topological space with a sheaf of commutative rings.
-- Morphisms of ringed spaces are the morphisms of `SheafedSpace CommRingCat`, carrying
-- the continuous base map (`RS.base`) and the comorphism of structure sheaves (`RS.c`).
--
-- Mathlib's `SheafOfModules` machinery is set up over a sheaf of rings
-- `R : TopCat.Sheaf RingCat X`; it provides the rank-one free module `SheafOfModules.unit`,
-- arbitrary free modules `SheafOfModules.free I = ⨁_{i ∈ I} unit`, the pushforward and
-- pullback functors (`SheafOfModules.pushforward`, `SheafOfModules.pullback`, the latter
-- being the left adjoint of the former, matching Definition 2), and sheafification. We
-- mirror the `AlgebraicGeometry.Scheme.Modules` development at the level of an arbitrary
-- ringed space.

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- The type of sheaves of `O_X`-modules on a ringed space `X`
(compare `AlgebraicGeometry.Scheme.Modules`). -/
@[ega "0 4.1.3" "special case",
  sga "2 I 1.7" "partial",
  sga "4 II 6.3.2" "special case",
  sga "4 IV 11.1.2" "special case",
  sga "4 V 3.5" "special case",
  sga "4 V 6.13" "special case",
  sga "6 II 2.0" "Mod for a ringed space",
  sga "6 II 2.3.2" "Mod(S), special case",
  sga "6 III 5.1" "special case"]
noncomputable abbrev RS.Modules (X : AlgebraicGeometry.RingedSpace.{u, u}) : Type _ :=
  SheafOfModules (ringCatSheaf X)

/-- The continuous base map underlying a morphism of ringed spaces. -/
@[ega "IV 8.2.8"]
noncomputable abbrev RS.base {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :
    (X : TopCat) ⟶ (Y : TopCat) :=
  ((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map f).base

/-- The comorphism of structure sheaves `O_Y → f_* O_X` underlying a morphism of ringed
spaces (the `f^\sharp` data). -/
noncomputable abbrev RS.c {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :=
  ((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map f).c

/-- The map of sheaves of rings obtained from a morphism of ringed spaces, packaged in the
form required by `SheafOfModules.pullback`/`SheafOfModules.pushforward`
(compare `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`). -/
noncomputable def RS.toRingCatSheafHom {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :
    ringCatSheaf Y ⟶
      ((Opens.map (RS.base f)).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
        (ringCatSheaf X) :=
  { hom := Functor.whiskerRight (RS.c f) (forget₂ CommRingCat RingCat) }

/-- Definition 2: the pullback functor `f^*` on sheaves of modules along a morphism `f`
of ringed spaces. It is defined as `SheafOfModules.pullback`, which is the left adjoint of
the pushforward, i.e. `f^*G = sheafification(f^{-1}G ⊗_{f^{-1}O_Y} O_X)`
(compare `AlgebraicGeometry.Scheme.Modules.pullback`). -/
@[ega "0 4.3.1",
  sga "3 I 4.6.1" "more general",
  sga "3 III 0.1.4" "more general",
  sga "4 IV 13.2.2" "special case",
  sga "4 XVII 4.1" "special case",
  sga "6 VI 2.3.1" "more general",
  sga "7 XIV 4.5" "more general"]
noncomputable def RS.Modules.pullback {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :
    RS.Modules Y ⥤ RS.Modules X :=
  SheafOfModules.pullback (RS.toRingCatSheafHom f)

/-- The restriction `M|_U` of a sheaf of `O_X`-modules `M` to an open subset `U ⊆ X`,
viewed as a sheaf of `O_X|_U`-modules on the open ringed subspace `X.restrict U`. It is
the pullback along the open-immersion inclusion `X.restrict U ⟶ X`. -/
@[ega "IV 21.13.3"]
noncomputable def RS.Modules.restrict {X : AlgebraicGeometry.RingedSpace.{u, u}} (M : RS.Modules X)
    (U : Opens X) : RS.Modules (X.restrict U.isOpenEmbedding) :=
  (RS.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj M

/-- Definition 1 (locally free, Tag 01C6): a sheaf of `O_X`-modules `M` is locally free if
every point `x ∈ X` has an open neighbourhood `U` such that the restriction `M|_U` is
isomorphic, as a sheaf of `O_X|_U`-modules, to a free module `⨁_{i ∈ I} (O_X|_U)` for some
index type `I` (allowed to be arbitrary and to depend on `x`).

No finiteness is imposed on `I`, nor any bound on its cardinality: it ranges over all of
`Type u`, the universe in which the structure sheaf of `X` takes its values and hence the only
one in which `SheafOfModules.free` forms a direct sum of copies of `O_X|_U`. The finite and
fixed-rank refinements, parts (2) and (3) of the same definition, are
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and `.IsFiniteLocallyFreeOfRank`. -/
@[stacks 01C6 "part (1), locally free with an arbitrary index set",
  ega "0 5.4.1",
  ega "III 7.9.1",
  ega "IV 2.1.12",
  ega "IV 21.5.3" "partial"]
def RS.Modules.IsLocallyFree {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (M : RS.Modules X) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (I : Type u),
    Nonempty (M.restrict U ≅ SheafOfModules.free I)

/-! ### Decomposition into sub-lemmas (proof sketch for Tag 01C8)

The informal proof: given `x : X`, set `y = f x`, choose `V ∋ y` with
`G|_V ≅ free I`, and put `U = f⁻¹(V)`. Then
`(f^*G)|_U ≅ (f|_U)^*(G|_V) ≅ (f|_U)^*(free I) ≅ free I`. The three isos used are:
pullback commutes with restriction to opens (pseudofunctoriality), pullback preserves
arbitrary direct sums (it is a left adjoint), and pullback sends the structure sheaf to
the structure sheaf (`f^* O_Y ≅ O_X`).

We isolate the genuinely hard content in named sub-lemmas:

* `RS.Modules.pullback_obj_free_iso` — pullback of a free module is free, for an
  *arbitrary* morphism of ringed spaces. (The two Mathlib facts behind it,
  `SheafOfModules.pullbackObjUnitToUnit` being iso and `SheafOfModules.pullbackObjFreeIso`,
  require finality of the site functor `Opens.map (base f)`, which fails for general `f`;
  the geometric statement `f^* O_Y ≅ O_X`, hence `f^* (⨁_I O_Y) ≅ ⨁_I O_X`, nonetheless
  holds for all `f`. This is the analytic kernel.)
* `RS.Modules.pullback_comp_iso` — pseudofunctoriality: `(g ≫ h)^* ≅ g^* ∘ h^*` on
  modules. (Mathlib has `SheafOfModules.pullbackComp`; we transport it through
  `RS.toRingCatSheafHom`, which is functorial.)
* `RS.Modules.pullback_map_iso` — pullback of an iso is an iso (purely formal hook).

The localization base-change iso
`((pullback f).obj G).restrict U ≅ (pullback f').obj (G.restrict V)` (for `U = f⁻¹(V)`
and `f' : X.restrict U ⟶ Y.restrict V` the corestriction of `f`) is assembled inline in
`pullback_isLocallyFree` from `pullback_comp_iso` and the factorization `j_U ≫ f = f' ≫ j_V`.
-/

/-- Pseudofunctoriality of pullback on sheaves of `O`-modules over ringed spaces:
pulling back along a composite `g ≫ h` is (naturally isomorphic to) pulling back along `h`
then along `g`. This transports `SheafOfModules.pullbackComp` (Mathlib) through the
functorial assignment `f ↦ RS.toRingCatSheafHom f`. -/
@[ega "0 4.3.6" "ringed spaces"]
noncomputable def RS.Modules.pullback_comp_iso {X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (M : RS.Modules Z) :
    (RS.Modules.pullback (g ≫ h)).obj M ≅
      (RS.Modules.pullback g).obj ((RS.Modules.pullback h).obj M) :=
  -- Mathlib: `SheafOfModules.pullbackComp φ ψ : pullback φ ⋙ pullback ψ ≅ pullback (φ ≫ …)`
  -- (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`). The induced ring-sheaf
  -- maps compose:
  -- `RS.toRingCatSheafHom (g ≫ h)` corresponds to
  -- `toRingCatSheafHom g ≫ (pushforward).map (toRingCatSheafHom h)` since `RS.c` is
  -- functorial (it is the comorphism component of a functor). Apply `pullbackComp` and
  -- rewrite the composite using that functoriality.  Compare the scheme-level
  -- `AlgebraicGeometry.Scheme.Modules.pullbackComp`, which is exactly this for schemes.
  (SheafOfModules.pullbackComp (RS.toRingCatSheafHom h) (RS.toRingCatSheafHom g)).symm.app M

/-- Pullback of a free module is free, for an arbitrary morphism of ringed spaces.
This is the analytic kernel: `f^*` sends the structure sheaf `O_Y` (i.e. `unit`) to `O_X`
(`unit`) — a consequence of `f^*G = f^{-1}G ⊗_{f^{-1}O_Y} O_X` with `G = O_Y` giving
`f^{-1}O_Y ⊗_{f^{-1}O_Y} O_X ≅ O_X` — and `f^*`, being a left adjoint, preserves the
coproduct `free I = ⨁_{i∈I} unit`. Mathlib proves exactly this as
`SheafOfModules.pullbackObjFreeIso` BUT under the extra hypothesis that the site functor
`Opens.map (base f)` is `Final`, which holds for open immersions (it is then a right
adjoint via `IsOpenMap.adjunction`) but not for general `f`. The map
`SheafOfModules.pullbackObjUnitToUnit φ : (pullback φ).obj unit ⟶ unit` always exists; one
must show it is an iso for arbitrary `f` (its `IsIso` instance uses
`bijective_pushforwardSections`/finality, so a finality-free argument — e.g. via stalks,
since `(f^*M)_x ≅ M_{f x} ⊗_{O_{Y,f x}} O_{X,x}` and `unit` has stalk `O`, giving an iso on
all stalks — is required), then transport along the coproduct decomposition of `free`. -/
@[ega "0 5.1.4" "partial",
  ega "0 5.2.4" "partial",
  ega "0 5.4.5" "more general",
  ega "II 6.4.8" "special case",
  ega "III 6.10.5" "partial", sga "4 IV 13.4" "special case"]
noncomputable def RS.Modules.pullback_obj_free_iso {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : X ⟶ Y) (I : Type _) :
    (RS.Modules.pullback f).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  -- The site functor `Opens.map (base f)` is representably flat (it has a left adjoint and
  -- preserves finite limits, as `g⁻¹` commutes with finite intersections), hence `Final`.
  -- With this finality instance available, Mathlib's `SheafOfModules.pullbackObjFreeIso`
  -- applies directly: it provides exactly `(pullback φ).obj (free I) ≅ free I`.
  haveI : (Opens.map (RS.base f)).Final := CategoryTheory.final_of_representablyFlat _
  SheafOfModules.pullbackObjFreeIso (RS.toRingCatSheafHom f) I

/-- Pulling back the witness iso `G.restrict V ≅ free I` along the corestricted map `f'`
is again an iso: functors preserve isomorphisms, so this is `Functor.mapIso (pullback f') e`.
It is one step of the localization chain in `pullback_isLocallyFree`. -/
@[ega "IV 21.3.2" "partial"]
noncomputable def RS.Modules.pullback_map_iso {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : X ⟶ Y) {M N : RS.Modules Y} (e : M ≅ N) :
    (RS.Modules.pullback f).obj M ≅ (RS.Modules.pullback f).obj N :=
  (RS.Modules.pullback f).mapIso e

/-- Statement 1 (Stacks Tag 01C8, Lemma 17.14.3): the pullback `f^*G` of a locally free
sheaf of modules `G` along a morphism of ringed spaces `f` is locally free. -/
@[stacks 01C8,
  ega "0 5.4.5" "locally free case",
  ega "II 6.4.8" "partial",
  ega "IV 8.5.5" "Sufficiency"]
theorem pullback_isLocallyFree {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : RS.Modules Y) (hG : RS.Modules.IsLocallyFree G) :
    RS.Modules.IsLocallyFree ((RS.Modules.pullback f).obj G) := by
  -- Fix `x : X` and let `y = f x`.
  intro x
  -- Local trivialization of `G` at `y = (RS.base f) x`: get `V ∋ y`, `I`, `G|_V ≅ free I`.
  obtain ⟨V, hyV, I, ⟨e⟩⟩ := hG ((RS.base f) x)
  -- Set `U = f⁻¹(V)`, an open neighbourhood of `x` since `f x = y ∈ V`.
  refine ⟨(Opens.map (RS.base f)).obj V, hyV, I, ⟨?_⟩⟩
  -- Goal: `((pullback f).obj G).restrict U ≅ free I` where `U = f⁻¹(V)`.
  --
  -- The localization step. Write `j_U : X.restrict U ⟶ X` and `j_V : Y.restrict V ⟶ Y`
  -- for the open-immersion inclusions, so `restrict _ U = (pullback j_U).obj _` and
  -- `restrict _ V = (pullback j_V).obj _`. Because `U = f⁻¹(V)`, the morphism `j_U ≫ f`
  -- factors through `j_V`: there is a (corestricted) morphism `f' : X.restrict U ⟶
  -- Y.restrict V` with `j_U ≫ f = f' ≫ j_V`. Then, using `pullback_comp_iso` twice
  -- (pseudofunctoriality) and `pullbackCongr` on the equal composites:
  --   ((pullback f).obj G).restrict U
  --     = (pullback j_U).obj ((pullback f).obj G)
  --     ≅ (pullback (j_U ≫ f)).obj G                       [pullback_comp_iso, symm]
  --     ≅ (pullback (f' ≫ j_V)).obj G                      [j_U ≫ f = f' ≫ j_V]
  --     ≅ (pullback f').obj ((pullback j_V).obj G)         [pullback_comp_iso]
  --     = (pullback f').obj (G.restrict V)
  --     ≅ (pullback f').obj (free I)                       [pullback_map_iso f' e]
  --     ≅ free I.                                          [pullback_obj_free_iso f' I]
  --
  -- NOTE the orientation of `RS.Modules.pullback (g ≫ h)`: with `g : X ⟶ Y`, `h : Y ⟶ Z`,
  -- `pullback (g ≫ h) : Modules Z ⥤ Modules X` and `pullback_comp_iso g h M :
  -- (pullback (g ≫ h)).obj M ≅ (pullback g).obj ((pullback h).obj M)`. Here the relevant
  -- composite is `j_U ≫ f : X.restrict U ⟶ Y` (i.e. `g = j_U`, `h = f`), and
  -- `f' ≫ j_V : X.restrict U ⟶ Y` (i.e. `g = f'`, `h = j_V`). The needed equality of
  -- ringed-space morphisms `j_U ≫ f = f' ≫ j_V` is the universal property of the open
  -- immersion `j_V` (`IsOpenImmersion`/`Scheme.Hom.restrict`-style factorization); `f'`
  -- itself is constructed from `f` and the inclusion `U ⊆ f⁻¹(V)` (here an equality).
  set U : Opens X := (Opens.map (RS.base f)).obj V
  set jU : X.restrict U.isOpenEmbedding ⟶ X := X.ofRestrict U.isOpenEmbedding
  set jV : Y.restrict V.isOpenEmbedding ⟶ Y := Y.ofRestrict V.isOpenEmbedding
  let F := SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)
  -- Range condition: `f(U) ⊆ V`, since `U = f⁻¹(V)`.
  have H : Set.range (ConcreteCategory.hom (F.map (jU ≫ f)).base) ⊆
      Set.range (ConcreteCategory.hom (F.map jV).base) := by
    rw [show Set.range (ConcreteCategory.hom (F.map jV).base) = (V : Set Y) from
      Opens.set_range_inclusion' V, Set.range_subset_iff, F.map_comp]
    intro u
    show (ConcreteCategory.hom (F.map f).base) ((ConcreteCategory.hom (F.map jU).base) u) ∈ V
    exact (Opens.set_range_inclusion' U).subset (Set.mem_range_self u)
  -- The corestriction `f' : X.restrict U ⟶ Y.restrict V`, obtained by lifting `jU ≫ f`
  -- along the open immersion `jV`, transported back to `RingedSpace` via full faithfulness
  -- of `forgetToPresheafedSpace`.
  let glift : F.obj (X.restrict U.isOpenEmbedding) ⟶ F.obj (Y.restrict V.isOpenEmbedding) :=
    PresheafedSpace.IsOpenImmersion.lift (F.map jV) (F.map (jU ≫ f)) H
  let f' : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding := F.preimage glift
  -- The factorization `jU ≫ f = f' ≫ jV`.
  have hfac : jU ≫ f = f' ≫ jV := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, show F.map f' = glift from F.map_preimage glift]
    exact (PresheafedSpace.IsOpenImmersion.lift_fac (F.map jV) (F.map (jU ≫ f)) H).symm
  -- Assemble the localization chain.
  exact (RS.Modules.pullback_comp_iso jU f G).symm ≪≫ eqToIso (by rw [hfac]) ≪≫
    RS.Modules.pullback_comp_iso f' jV G ≪≫ RS.Modules.pullback_map_iso f' e ≪≫
    RS.Modules.pullback_obj_free_iso f' I

/-- Correctness of Definition 2: the pullback functor agrees definitionally with the
Mathlib pullback of sheaves of modules along the induced map of sheaves of rings. -/
theorem RS.Modules.pullback_eq {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :
    RS.Modules.pullback f = SheafOfModules.pullback (RS.toRingCatSheafHom f) := rfl

/-- A free module is locally free: take `U = X`. -/
theorem free_isLocallyFree {X : AlgebraicGeometry.RingedSpace.{u, u}} (I : Type _) :
    RS.Modules.IsLocallyFree (X := X) (SheafOfModules.free I) := by
  -- Take `U = ⊤`. Then `(free I).restrict ⊤ = (pullback (ofRestrict ⊤)).obj (free I)`,
  -- and pullback of free is free by `pullback_obj_free_iso` applied to the open immersion
  -- `X.ofRestrict ⊤.isOpenEmbedding`. (Here the witness `free I` on the right lives over
  -- the restricted ringed space `X.restrict ⊤`, which is what `IsLocallyFree` requires.)
  exact fun _ ↦ ⟨⊤, trivial, I,
    ⟨RS.Modules.pullback_obj_free_iso (X.ofRestrict (⊤ : Opens X).isOpenEmbedding) I⟩⟩
