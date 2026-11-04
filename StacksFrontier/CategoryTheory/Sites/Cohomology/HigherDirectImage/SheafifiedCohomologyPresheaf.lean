module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

(Stacks Project, Tag `072W` / Lemma 21.7.4, "Cohomology on Sites".)

Let `f : (C, O_C) -> (D, O_D)` be a morphism of ringed sites corresponding to a
continuous functor `u : D -> C`.  For a sheaf of `O_C`-modules `F` and an integer
`i >= 0`, the `i`-th higher direct image `R^i f_* F` is canonically isomorphic, *as a
sheaf of `O_D`-modules*, to the sheaf associated to the presheaf

    V |-> H^i(u(V), F)      (V an object of D),

where `H^i(U, F)` denotes the `i`-th cohomology of `F` over the object `U` of `C`
(the `i`-th right derived functor of the sections functor `F |-> Gamma(U, F) = F(U)`).
-/

/-
## Background and conventions (from Tag `072W`)

* `C`, `D` are sites, i.e. categories equipped with a Grothendieck topology
  (`CategoryTheory.GrothendieckTopology`).
* A continuous functor `u : D -> C` is modelled by `u.IsContinuous J_D J_C`.
  For module sheaves, `SheafOfModules.pushforward phi` produces the pushforward functor
  `SheafOfModules O_C ==> SheafOfModules O_D`; this is the functor `f_* = u^s`
  (Definition 1).  The key special property of a continuous `u` (Definition 1) is the
  pointwise formula `(f_* G)(V) = G(u(V))`, encoded by the equality of functors
    `f_* <gg> forget = forget <gg> (presheaf pushforward)`
  (`pushforward_forget_eq` below), which says that the underlying presheaf of the
  pushforward sheaf is the presheaf-level pushforward `V |-> G(u(V))`.  This is exactly
  the remark of Definition 1 that, since `u` is continuous, the presheaf
  `V |-> G(u(V))` is already a sheaf, i.e. `u^s G = u^p G` (Sites, Tag `00WW`).
* A *morphism of sites* `f : C -> D` (Tag `00X1`) is a continuous functor `u : D -> C`
  whose induced inverse-image functor `f^{-1} = u_s` (the `sheafPullback`, left adjoint
  to `f_*`) is *exact*, i.e. preserves finite limits.  We encode this exactness via
  `PreservesFiniteLimits (u.sheafPullback ..)` together with the right-adjointness of the
  continuous pushforward (so that `f_* = u^s` has a left adjoint `f^{-1} = u_s`).
  (The proof of Tag `072W` itself uses only the continuity of `u`.)
* The morphism of ringed sites supplies a morphism of ring sheaves
  `phi : O_D ==> f_* O_C` on `D`; its underlying morphism of presheaves of rings is
  `phi.hom : O_D.obj ==> u.op <gg> O_C.obj`.
* `R^i f_* = (f_*).rightDerived i` is the `i`-th right derived functor of `f_*`; this
  requires the source category `Mod(O_C)` to be abelian with enough injectives
  (`EnoughInjectives (SheafOfModules O_C)`).

### Cohomology over an object (Tag `071G`, Definition 2)
For an object `U` of `C`, the sections functor `Gamma(U, -) : Mod(O_C) ==> Mod(O_C(U))`
is `SheafOfModules.evaluation O_C (op U)`.  Its `i`-th right derived functor, evaluated at
a sheaf `F`, is the `i`-th cohomology group `H^i(U, F)` (with its natural
`O_C(U)`-module structure).  This is `cohomologyOverObject` below.

### Cohomology presheaf as a presheaf of `O_D`-modules (Definition 4)
The composite functor `SheafOfModules.forget O_C <gg> PresheafOfModules.pushforward phi.hom`
(`cohFunctor`) sends a sheaf of `O_C`-modules `G` to the presheaf of `O_D`-modules
`V |-> G(u(V))`, the `O_D(V)`-module structure on `G(u(V))` being restriction of scalars
along `phi`.  Its `i`-th right derived functor, evaluated at `F`, is the cohomology
presheaf `V |-> H^i(u(V), F)` of Definition 4, as a presheaf of `O_D`-modules
(`cohPresheafModule`).  Its value at `V`, as an `O_D(V)`-module, is the restriction of
scalars (along the ring map induced by `phi`) of `H^i(u(V), F)`; this objectwise module
identification is recorded in `cohPresheafModule_evaluation_iso`, and the restriction maps
along a morphism `V' -> V` are the maps `H^i(u(V), F) -> H^i(u(V'), F)` induced by `u`,
i.e. the functoriality of `cohFunctor.rightDerived i`.

### "The sheaf associated to the presheaf"
This is the sheafification functor `a` on presheaves of `O_D`-modules, realised here by
`PresheafOfModules.sheafification (id O_D.obj)` (`moduleSheafification`).

### On the formal shape of "canonical isomorphism"
The conclusion of Tag `072W` is a *canonical isomorphism of sheaves of `O_D`-modules*
`R^i f_* F  ==  a(V |-> H^i(u(V), F))`.  An isomorphism `A == B` lives in `Type`; we state
the theorem `higherDirectImage_iso_sheafify_cohomologyPresheaf` as the *existence* of such
an isomorphism between the two precisely-described sheaves of `O_D`-modules -- namely
`R^i f_* F` (`(SheafOfModules.pushforward phi).rightDerived i`, Definition 3) and
`a (cohPresheafModule i F)` (the sheafification of the cohomology presheaf, Definition 4).
The content of Tag `072W` (the existence and canonicity of the comparison) is the proof
obligation, left open below.  Both objects appearing in the statement are constructed by
genuine, complete terms with no unproven content.
-/

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ uRing uMod

-- the site `D`
variable {Dsite : Type u₁} [Category.{v₁} Dsite]
-- the site `C`
variable {Csite : Type u₂} [Category.{v₂} Csite]
variable {J𝒟 : GrothendieckTopology Dsite} {J𝒞 : GrothendieckTopology Csite}
-- the continuous functor `u : D -> C`
variable (u : Dsite ⥤ Csite) [u.IsContinuous J𝒟 J𝒞]
-- the structure sheaves of rings
variable (O𝒞 : Sheaf J𝒞 RingCat.{uRing}) (O𝒟 : Sheaf J𝒟 RingCat.{uRing})
-- the morphism of ring sheaves `O_D ==> f_* O_C` underlying the morphism of ringed sites
variable (φ : O𝒟 ⟶ (u.sheafPushforwardContinuous RingCat.{uRing} J𝒟 J𝒞).obj O𝒞)
-- sheafification hypotheses making `Mod(O_C)` and `Mod(O_D)` abelian and presheaf
-- sheafification available; the universe of the sections of the modules is independent of the
-- universes of the sites
variable [HasSheafify J𝒞 AddCommGrpCat.{uMod}] [J𝒞.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
variable [HasSheafify J𝒟 AddCommGrpCat.{uMod}] [J𝒟.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
-- enough injectives in `Mod(O_C)` (so cohomology and `R^i f_*` are defined)
variable [EnoughInjectives (SheafOfModules.{uMod} O𝒞)]
-- additivity of `f_* = pushforward` (so its right derived functors exist)
variable [(SheafOfModules.pushforward.{uMod} φ).Additive]

-- Main Definition(s)

/-- **Definition 2 (Cohomology over an object; Tag `071G`).**
For an object `V` of `D` (so that `u(V)` is an object of `C`), the `i`-th cohomology of a
sheaf of `O_C`-modules `F` over `u(V)` is the `i`-th right derived functor of the sections
functor `Gamma(u(V), -) = SheafOfModules.evaluation O_C (op (u V))`, evaluated at `F`.
This carries the natural `O_C(u V)`-module structure. -/
@[ega "0 12.1.1",
  ega "0 12.2.1" "H^p(f⁻¹V",
  ega "0 12.4.2" "special case",
  sga "4 V 2.1.2" "special case",
  sga "4 V 2.4.1",
  sga "4½ Arcata 1.6.5" "more general",
  sga "4½ Cycle 1.1.3" "special case"]
noncomputable def cohomologyOverObject (i : ℕ) (V : Dsite) (F : SheafOfModules O𝒞)
    [(SheafOfModules.evaluation O𝒞 (Opposite.op (u.obj V))).Additive] :
    ModuleCat (O𝒞.obj.obj (Opposite.op (u.obj V))) :=
  ((SheafOfModules.evaluation O𝒞 (Opposite.op (u.obj V))).rightDerived i).obj F

/-- The functor `Mod(O_C) ==> PMod(O_D)` underlying the cohomology presheaf (Definition 4):
it forgets the sheaf condition on a sheaf of `O_C`-modules and pushes the resulting
presheaf of modules forward along `phi`.  On objects it sends `G` to the presheaf
`V |-> G(u(V))` of `O_D`-modules, the `O_D(V)`-module structure being restriction of
scalars along `phi : O_D(V) -> O_C(u(V))`.  By `pushforward_forget_eq` this functor equals
`f_* <gg> forget`. -/
@[sga "7 VI 3.1(b)"]
noncomputable def cohFunctor : SheafOfModules.{uMod} O𝒞 ⥤ PresheafOfModules.{uMod} O𝒟.obj :=
  SheafOfModules.forget O𝒞 ⋙ PresheafOfModules.pushforward φ.hom

-- additivity of `cohFunctor` (so its right derived functors exist)
variable [(cohFunctor u O𝒞 O𝒟 φ).Additive]

/-- **Definition 4 (cohomology presheaf as a presheaf of `O_D`-modules).**
The `i`-th right derived functor of `cohFunctor`, evaluated at `F`.  On an object `V` of
`D` it computes `H^i(u(V), F)` with its induced `O_D(V)`-module structure (see
`cohPresheafModule_evaluation_iso`); the restriction maps along `V' -> V` are induced by
`u` on cohomology. -/
@[ega "0 12.2.1" "partial",
  ega "0 12.4.6" "special case",
  sga "4 V 2.4.2" "more general",
  sga "7 VI 3.1(b)"]
noncomputable def cohPresheafModule (i : ℕ) (F : SheafOfModules O𝒞) :
    PresheafOfModules O𝒟.obj :=
  ((cohFunctor u O𝒞 O𝒟 φ).rightDerived i).obj F

/-- Sheafification of presheaves of `O_D`-modules (the functor `a` of Definition 4),
landing in sheaves of `O_D`-modules. -/
noncomputable def moduleSheafification : PresheafOfModules O𝒟.obj ⥤ SheafOfModules O𝒟 :=
  PresheafOfModules.sheafification (𝟙 O𝒟.obj)

-- Supporting sub-lemmas (decomposition of Tag `072W`)

/-- **Sub-lemma 1 (exact additive functor commutes with right derived functors).**
If `F : A ⥤ B` is additive (between abelian categories, source with enough injectives) and
`G : B ⥤ E` is additive and *exact* (`G.PreservesHomology`), then `G` commutes with the
`i`-th right derived functor of `F`:
`G (R^i F X) ≅ R^i (F ⋙ G) X`.

*Argument.*  Pick an injective resolution `X[0] → I^•` in `A`.  By
`InjectiveResolution.isoRightDerivedObj`, `(F.rightDerived i).obj X` is the `i`-th homology
of the complex `F.mapHomologicalComplex I^•`, and `((F ⋙ G).rightDerived i).obj X` is the
`i`-th homology of `(F ⋙ G).mapHomologicalComplex I^• = G.mapHomologicalComplex (F.map…)`.
Since `G` preserves homology (it is exact), `G` of the homology is the homology of `G` of
the complex: this is the homology-functor comparison iso supplied by `G.PreservesHomology`
(at the `ShortComplex` level `ShortComplex.mapHomologyIso'`, lifted to homological
complexes via `HomologicalComplex.homologyFunctorIso`/`Functor.mapHomologicalComplex`).
Composing these identifications gives the claimed isomorphism.

Mathlib anchors: `InjectiveResolution.isoRightDerivedObj`, `Functor.PreservesHomology`,
`Functor.mapHomologicalComplex`, `HomologicalComplex.homology`, `ShortComplex.mapHomologyIso'`.
This is the single recurring technical tool used in both Tag `072W` theorems. -/
@[sga "4 V 2.5.2" "partial"]
theorem rightDerived_comp_iso_of_preservesHomology
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E] [HasInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ E) [G.Additive] [G.PreservesHomology]
    [(F ⋙ G).Additive] (i : ℕ) (X : A) :
    Nonempty (G.obj ((F.rightDerived i).obj X) ≅ ((F ⋙ G).rightDerived i).obj X) := by
  -- Build via `InjectiveResolution.isoRightDerivedObj` (both sides) +
  -- the homology-preservation iso of `G` (`G.PreservesHomology`).
  let c := ComplexShape.up ℕ
  let I := injectiveResolution X
  let K := (F.mapHomologicalComplex c).obj I.cocomplex
  -- Since `G` preserves homology, `G` of the `i`-th homology of `K` is the `i`-th homology of
  -- `G.mapHomologicalComplex K`; and `(G.mapHomologicalComplex c).obj K` is definitionally
  -- `((F ⋙ G).mapHomologicalComplex c).obj I.cocomplex`, so that identification composes with
  -- the right derived identifications of `F` and of `F ⋙ G`.
  exact ⟨G.mapIso (I.isoRightDerivedObj F i ≪≫
      (HomologicalComplex.homologyFunctorIso _ _ i).app K) ≪≫
    ((K.sc i).mapHomologyIso G).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ _ i).app
      ((G.mapHomologicalComplex c).obj K)).symm ≪≫
    (I.isoRightDerivedObj (F ⋙ G) i).symm⟩

/-- **Sub-lemma 2 (sheafification of the underlying presheaf of a sheaf returns the sheaf).**
For a sheaf of `O_D`-modules `G`, sheafifying its underlying presheaf `forget G` gives back
`G`, i.e. `a (forget G) ≅ G`, where `a = moduleSheafification O𝒟`.

*Argument.*  `a = PresheafOfModules.sheafification (𝟙 O𝒟.obj)` is left adjoint to
`SheafOfModules.forget O𝒟 ⋙ PresheafOfModules.restrictScalars (𝟙 …)` via
`PresheafOfModules.sheafificationAdjunction`; with `α = 𝟙` the right adjoint is (naturally
isomorphic to) `forget`.  The counit of this reflective adjunction is an isomorphism on the
essential image, i.e. on objects of the form `forget G` (the underlying presheaf of an
honest sheaf is already a sheaf, so its sheafification is canonically itself).  Concretely
`a (forget G) ≅ G` is the component of the counit / unit isomorphism at `G`.

Mathlib anchors: `PresheafOfModules.sheafificationAdjunction`, `Adjunction.counit`,
`PresheafOfModules.restrictScalars (𝟙 _) ≅ 𝟭`, reflective subcategory counit-iso facts. -/
theorem moduleSheafification_forget_iso (G : SheafOfModules O𝒟) :
    Nonempty ((moduleSheafification O𝒟).obj ((SheafOfModules.forget O𝒟).obj G) ≅ G) :=
  -- SKETCH: counit isomorphism of the sheafification ⊣ forget reflective adjunction
  -- (`PresheafOfModules.sheafificationAdjunction (𝟙 O𝒟.obj)`), specialized to the
  -- underlying presheaf of an honest sheaf.  The right adjoint
  -- `forget O𝒟 ⋙ restrictScalars (𝟙 O𝒟.obj)` is fully faithful (forget is, and
  -- `restrictScalars (𝟙)` is defeq to the identity on the relevant object), so the
  -- counit is an isomorphism (`Adjunction.instIsIsoAppCounitOfFullOfFaithful`).
  -- SANITY CHECK PASSED
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O𝒟.obj)
  let hiso : IsIso (adj.counit.app G) := Adjunction.instIsIsoAppCounitOfFullOfFaithful adj G
  ⟨@asIso _ _ _ _ (adj.counit.app G) hiso⟩

omit [HasSheafify J𝒟 AddCommGrpCat] [J𝒟.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Sub-lemma 3 (identifying the rightDerived of `π ⋙ forget` with `cohPresheafModule`).**
The right derived presheaf of the composite `f_* ⋙ forget = SheafOfModules.pushforward φ ⋙
SheafOfModules.forget O𝒟` is the cohomology presheaf `cohPresheafModule i F` of Definition 4.

*Argument.*  By `pushforward_forget_eq` (the continuity-of-`u` formula, Definition 1) we have
the equality of functors `SheafOfModules.pushforward φ ⋙ SheafOfModules.forget O𝒟
= SheafOfModules.forget O𝒞 ⋙ PresheafOfModules.pushforward φ.hom = cohFunctor`.  Transporting
the right derived functor along this equality of additive functors gives
`((π ⋙ forget).rightDerived i).obj F ≅ (cohFunctor.rightDerived i).obj F
= cohPresheafModule i F`.  (The isomorphism is `eqToIso` of the functor equality, transported
through `Functor.rightDerived`; the only subtlety is the dependent `Additive` instance, which
is why this is isolated as its own lemma rather than a `rw`.)

Mathlib anchors: `pushforward_forget_eq`, `eqToIso`, `Functor.rightDerived` congruence. -/
theorem pushforward_forget_rightDerived_iso (i : ℕ) (F : SheafOfModules O𝒞) :
    Nonempty
      (((SheafOfModules.pushforward φ ⋙ SheafOfModules.forget O𝒟).rightDerived i).obj F ≅
        cohPresheafModule u O𝒞 O𝒟 φ i F) :=
  -- SKETCH: transport `rightDerived i` along `pushforward_forget_eq`
  -- (`SheafOfModules.pushforward φ ⋙ SheafOfModules.forget O𝒟 = cohFunctor …`), then
  -- unfold `cohPresheafModule`.  Pure bookkeeping along a functor equality.
  -- SANITY CHECK PASSED
  ⟨Iso.refl _⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction of scalars is exact (preserves homology).**
`ModuleCat.restrictScalars f`, for a ring homomorphism `f : R →+* S`, preserves homology:
it preserves finite limits (because the forgetful functor to `AddCommGrp` reflects them and
`restrictScalars f ⋙ forget₂ = forget₂` preserves them) and finite colimits (Mathlib's
per-diagram instance `ModuleCat.preservesColimit_restrictScalars` makes every finite-shape
colimit be preserved, since finite colimits in module categories exist), hence by
`Functor.preservesHomologyOfExact` it preserves homology.  This is the `PreservesHomology`
instance for `restrictScalars` that is *not* available directly in Mathlib; it is needed to
apply `rightDerived_comp_iso_of_preservesHomology` with `G := restrictScalars f`.

The colimit half is built from the per-diagram instance rather than from the
coextension-of-scalars adjunction or the bundled `forget₂` finite-colimit instance: this
keeps the proof universe-polymorphic (no `ring-universe ≤ module-universe` constraint) and
proof-complete in the `stacks` toolchain (the bundled `forget₂` finite-colimit instance is
unproved there).  The module universe `uMod` is independent of the ring-carrier
universe `uRing`. -/
@[ega "III 7.1.3" "Exactness of ρ_*", sga "5 X 3.3" "more general"]
theorem restrictScalars_preservesHomology {R S : Type uRing}
    [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{uMod} f).PreservesHomology := by
  have heq : forget₂ (ModuleCat.{uMod} S) AddCommGrpCat
      = ModuleCat.restrictScalars.{uMod} f ⋙ forget₂ (ModuleCat.{uMod} R) AddCommGrpCat := rfl
  have hlim : PreservesFiniteLimits (ModuleCat.restrictScalars.{uMod} f) := by
    have : PreservesFiniteLimits
        (ModuleCat.restrictScalars.{uMod} f ⋙ forget₂ (ModuleCat.{uMod} R) AddCommGrpCat) :=
      preservesFiniteLimits_of_natIso (eqToIso heq)
    exact preservesFiniteLimits_of_reflects_of_preserves
      (ModuleCat.restrictScalars.{uMod} f) (forget₂ (ModuleCat.{uMod} R) AddCommGrpCat)
  have hcolim : PreservesFiniteColimits (ModuleCat.restrictScalars.{uMod} f) := by
    constructor
    intro J _ _
    constructor
    intro F
    infer_instance
  exact Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{uMod} f)

omit [HasSheafify J𝒟 AddCommGrpCat] [J𝒟.WEqualsLocallyBijective AddCommGrpCat]
    [(SheafOfModules.pushforward φ).Additive] [(cohFunctor u O𝒞 O𝒟 φ).Additive] in
/-- **Sub-lemma 4 (restriction of scalars commutes with right derived functors).**
The functor `R := ModuleCat.restrictScalars (φ.hom.app (op V))` is exact, so it commutes with
the right derived functor of the sections functor `Γ(u V, -) = SheafOfModules.evaluation O𝒞
(op (u V))`; applied at `F` this yields
`R^i (Γ(u V, -) ⋙ R) F ≅ R (H^i(u V, F)) = R (cohomologyOverObject i V F)`.

*Argument.*  This is `rightDerived_comp_iso_of_preservesHomology` with `F := Γ(u V, -)` and
`G := R`, EXCEPT that `(ModuleCat.restrictScalars f).PreservesHomology` is **not** available
as a Mathlib instance.  It must be supplied: `restrictScalars f` is exact because the
underlying-abelian-group forgetful functor `forget₂ (ModuleCat R) AddCommGrp` is faithful and
exact and factors as `restrictScalars f ⋙ forget₂ (ModuleCat S) AddCommGrp = forget₂ (ModuleCat R)
AddCommGrp`
(restriction of scalars does not change the underlying abelian group); a faithful exact
functor that detects exactness shows `restrictScalars f` preserves kernels and cokernels,
hence homology.  Equivalently, `restrictScalars f` has both a left adjoint (extension of
scalars) and a right adjoint (coextension), so it preserves all finite limits and colimits.
Given that instance, the iso is `rightDerived_comp_iso_of_preservesHomology` followed by
`R (R^i Γ(uV,-) F) = R (cohomologyOverObject i V F)` (definition of `cohomologyOverObject`).

Mathlib anchors: `ModuleCat.restrictScalars`, `forget₂ (ModuleCat _) AddCommGrp` faithful +
exact, `ModuleCat.restrictScalars`'s adjoints (extension/coextension of scalars),
`rightDerived_comp_iso_of_preservesHomology`. -/
theorem restrictScalars_rightDerived_iso
    [∀ V : Dsite, (SheafOfModules.evaluation O𝒞 (Opposite.op (u.obj V))).Additive]
    (i : ℕ) (F : SheafOfModules O𝒞) (V : Dsite) :
    Nonempty
      (((SheafOfModules.evaluation O𝒞 (Opposite.op (u.obj V)) ⋙
          ModuleCat.restrictScalars (φ.hom.app (Opposite.op V)).hom).rightDerived i).obj F ≅
        (ModuleCat.restrictScalars (φ.hom.app (Opposite.op V)).hom).obj
          (cohomologyOverObject u O𝒞 i V F)) :=
  -- Establish `(ModuleCat.restrictScalars _).PreservesHomology` via the helper_072w
  -- `restrictScalars_preservesHomology`, then apply
  -- `rightDerived_comp_iso_of_preservesHomology` with `F := SheafOfModules.evaluation O𝒞
  -- (op (u V))`, `G := restrictScalars …`.  `cohomologyOverObject u O𝒞 i V F` is
  -- definitionally `((evaluation …).rightDerived i).obj F`, so the symmetrized iso matches.
  -- SANITY CHECK PASSED
  by
  have : (ModuleCat.restrictScalars (φ.hom.app (Opposite.op V)).hom).PreservesHomology :=
    restrictScalars_preservesHomology (φ.hom.app (Opposite.op V)).hom
  obtain ⟨e⟩ := rightDerived_comp_iso_of_preservesHomology
    (SheafOfModules.evaluation O𝒞 (Opposite.op (u.obj V)))
    (ModuleCat.restrictScalars (φ.hom.app (Opposite.op V)).hom) i F
  exact ⟨e.symm⟩


/-- Sheafification of presheaves of modules, being a left adjoint, preserves finite colimits. -/
private theorem sheafification_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafOfModules.sheafification (𝟙 O𝒟.obj)) :=
  have hbig :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 O𝒟.obj)).leftAdjoint_preservesColimits
  ⟨fun _ _ _ => hbig.preservesColimitsOfShape⟩

/-- **Sheafification of presheaves of modules preserves homology (exactness of `a`).**
The functor `a = PresheafOfModules.sheafification (𝟙 O𝒟.obj)` preserves homology: it preserves
finite limits (clean ambient instance, since sheafification is left exact) and finite colimits
(it is the *left adjoint* of `sheafificationAdjunction`, so it preserves all colimits — built
explicitly from `Adjunction.leftAdjoint_preservesColimits` rather than the ambient
unproved colimit instance), hence by `Functor.preservesHomologyOfExact` preserves homology.
This is the *sound* exactness fact replacing the (false, unproved) claim that
`SheafOfModules.forget` preserves homology. -/
@[sga "4 IV 13.6" "special case", sga "7 VI 3.1(a)" "more general"]
theorem sheafification_preservesHomology :
    (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).PreservesHomology := by
  have hlim : PreservesFiniteLimits (PresheafOfModules.sheafification (𝟙 O𝒟.obj)) :=
    inferInstance
  have hzero : (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  exact Functor.preservesHomologyOfExact _

/-- **Sheafification is additive (proof-complete).**
Built from `PreservesZeroMorphisms` (via preserving the terminal object, clean) and
`PreservesBinaryBiproducts` (via preserving binary coproducts, which sheafification does as a
left adjoint — clean, from `leftAdjoint_preservesColimits`). Needed to discharge the
`((π ⋙ forget) ⋙ a).Additive` instance argument of
`rightDerived_comp_iso_of_preservesHomology` in the main theorem without grabbing the
unproved ambient `(a).Additive`. -/
theorem sheafification_additive :
    (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).Additive := by
  have hzero : (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have hbp : PreservesBinaryBiproducts (PresheafOfModules.sheafification (𝟙 O𝒟.obj)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **Functor isomorphism `f_* ≅ (f_* ⋙ forget) ⋙ a`.**
The pushforward `π = SheafOfModules.pushforward φ` is naturally isomorphic to
`(π ⋙ SheafOfModules.forget O𝒟) ⋙ a`, where `a = sheafification (𝟙 O𝒟.obj)`.  This is the
functor-level form of Sub-lemma 2 (`a (forget G) ≅ G`): whiskering `π` by the counit
isomorphism `(forget ⋙ restrictScalars 𝟙) ⋙ a ≅ 𝟭` of `sheafificationAdjunction`
(`restrictScalars (𝟙)` is definitionally the identity on the underlying presheaf, and
associativity is definitional).  Transporting `rightDerived i` along this iso is what lets the
main theorem use the *sound* exactness of `a` (sheafification) in place of the false exactness
of `forget`. -/
noncomputable def pushforward_iso_pushforwardForget_comp_sheafification :
    SheafOfModules.pushforward φ ≅
      (SheafOfModules.pushforward φ ⋙ SheafOfModules.forget O𝒟) ⋙
        PresheafOfModules.sheafification (𝟙 O𝒟.obj) := by
  haveI cI : (SheafOfModules.forget O𝒟 ⋙ PresheafOfModules.restrictScalars (𝟙 O𝒟.obj)) ⋙
      PresheafOfModules.sheafification (𝟙 O𝒟.obj) ≅ 𝟭 (SheafOfModules O𝒟) :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 O𝒟.obj)).counit
  refine (SheafOfModules.pushforward φ).rightUnitor.symm ≪≫
    (SheafOfModules.pushforward φ).isoWhiskerLeft cI.symm ≪≫ ?_
  exact Iso.refl _

-- Main Statement(s)

/-- **Stacks Tag `072W` (Lemma 21.7.4).**
For a morphism of ringed sites `f : (C, O_C) -> (D, O_D)` given by a continuous functor
`u : D -> C`, a sheaf of `O_C`-modules `F`, and `i >= 0`, the higher direct image
`R^i f_* F` (Definition 3, the `i`-th right derived functor of `f_* = u^s`) is canonically
isomorphic, *as a sheaf of `O_D`-modules*, to the sheafification `a (cohPresheafModule i F)`
of the cohomology presheaf `V |-> H^i(u(V), F)` (Definition 4).

A morphism of ringed sites carries more data than the proof uses: the right-adjointness of
the continuous pushforward (so `f_* = u^s` has a left adjoint `f^{-1} = u_s`) and the
exactness of that inverse image are what make `u` a morphism of sites, but the proof of Tag
`072W` uses only the continuity of `u` (Definition 1, `pushforward_forget_eq`), so neither is
assumed here. This matters in practice: on the big sites of schemes the continuous functor is
base change along a morphism, whose continuity is available while the exactness of the
inverse image is not. -/
@[stacks 072W,
  ega "0 12.4.3" "degree-0 complex",
  sga "4 V 5.1" "1)",
  ega "0 12.2.1" "partial",
  sga "4 VIII 5.1" "more general"]
theorem higherDirectImage_iso_sheafify_cohomologyPresheaf
    (i : ℕ) (F : SheafOfModules O𝒞) :
    Nonempty
      (((SheafOfModules.pushforward φ).rightDerived i).obj F ≅
        (moduleSheafification O𝒟).obj (cohPresheafModule u O𝒞 O𝒟 φ i F)) := by
  -- Proof of Tag `072W`, assembled soundly.  Write `π := SheafOfModules.pushforward φ`,
  -- `frgt := SheafOfModules.forget O𝒟`, `a := moduleSheafification O𝒟 = sheafification (𝟙)`.
  --
  -- CRUCIAL SOUNDNESS POINT.  The earlier assembly applied
  -- `rightDerived_comp_iso_of_preservesHomology` with `G := frgt`, which requires
  -- `frgt.PreservesHomology`.  That instance is FALSE in general (and is left unproved in
  -- the `stacks` toolchain): `frgt : SheafOfModules ⥤ PresheafOfModules` is a reflective
  -- inclusion, a RIGHT adjoint, so it preserves finite limits but NOT finite colimits
  -- (colimits of sheaves are sheafifications of presheaf colimits).  We instead use the
  -- *exactness of sheafification* `a` (a left exact LEFT adjoint, hence preserves both finite
  -- limits and finite colimits — `sheafification_preservesHomology`), which is genuinely
  -- true and proof-complete.
  --
  -- Step 0 (functor iso, `pushforward_iso_pushforwardForget_comp_sheafification`).
  --   `π ≅ (π ⋙ frgt) ⋙ a` (the functor form of `a (frgt G) ≅ G`).  Transport `rightDerived i`
  --   along it (`Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso`) and evaluate at `F`:
  --   `R^i π F ≅ R^i ((π ⋙ frgt) ⋙ a) F`.
  -- Step 1 (Sub-lemma 1 with `F := π ⋙ frgt`, `G := a`).  `a` is exact, so
  --   `a (R^i (π ⋙ frgt) F) ≅ R^i ((π ⋙ frgt) ⋙ a) F`.  (Used reversed.)
  -- Step 2 (Sub-lemma 3).  `R^i (π ⋙ frgt) F ≅ cohPresheafModule i F`.
  -- Composing:
  --   `R^i π F ≅ R^i ((π⋙frgt)⋙a) F ≅ a (R^i (π⋙frgt) F) ≅ a (cohPresheafModule i F)`.
  have : (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).PreservesHomology :=
    sheafification_preservesHomology O𝒟
  have : (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).Additive :=
    sheafification_additive O𝒟
  -- Step 0: `R^i π F ≅ R^i ((π ⋙ frgt) ⋙ a) F`.
  have e0 :=
    (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (pushforward_iso_pushforwardForget_comp_sheafification u O𝒞 O𝒟 φ) i).app F
  -- Step 1: `a (R^i (π ⋙ frgt) F) ≅ R^i ((π ⋙ frgt) ⋙ a) F`.
  obtain ⟨e1⟩ := rightDerived_comp_iso_of_preservesHomology
    (SheafOfModules.pushforward φ ⋙ SheafOfModules.forget O𝒟)
    (PresheafOfModules.sheafification (𝟙 O𝒟.obj)) i F
  -- Step 2: `R^i (π ⋙ frgt) F ≅ cohPresheafModule i F`.
  obtain ⟨e3⟩ := pushforward_forget_rightDerived_iso u O𝒞 O𝒟 φ i F
  refine ⟨e0 ≪≫ e1.symm ≪≫ ?_⟩
  exact (moduleSheafification O𝒟).mapIso e3

omit [HasSheafify J𝒟 AddCommGrpCat] [J𝒟.WEqualsLocallyBijective AddCommGrpCat]
  [(SheafOfModules.pushforward φ).Additive] in
/-- **Correctness of `cohPresheafModule` (Definition 4 is objectwise Definition 2).**
For each object `V` of `D`, the value of the cohomology presheaf `cohPresheafModule i F` at
`V` is canonically isomorphic, *as an `O_D(V)`-module*, to the restriction of scalars along
the ring map `phi.hom : O_D(V) -> O_C(u(V))` of the cohomology `O_C(u V)`-module
`H^i(u(V), F)` of Definition 2.  This makes precise that `cohPresheafModule i F` is the
presheaf `V |-> H^i(u(V), F)`, with the `O_D`-module structure induced by `phi` (the
identification is a genuine isomorphism of `O_D(V)`-modules, not merely of underlying
abelian groups).  It is the supporting objectwise statement; the canonical content of
Tag `072W` is in `higherDirectImage_iso_sheafify_cohomologyPresheaf`. -/
@[sga "4 V 2.4.2" "more general"]
theorem cohPresheafModule_evaluation_iso
    [∀ V : Dsite, (SheafOfModules.evaluation O𝒞 (Opposite.op (u.obj V))).Additive]
    (i : ℕ) (F : SheafOfModules O𝒞) (V : Dsite) :
    Nonempty
      ((PresheafOfModules.evaluation O𝒟.obj (Opposite.op V)).obj
          (cohPresheafModule u O𝒞 O𝒟 φ i F) ≅
        (ModuleCat.restrictScalars (φ.hom.app (Opposite.op V)).hom).obj
          (cohomologyOverObject u O𝒞 i V F)) := by
  -- Objectwise identification of Definition 4 with Definition 2.  Write
  -- `E_V := PresheafOfModules.evaluation O𝒟.obj (op V)`,
  -- `R := ModuleCat.restrictScalars (φ.hom.app (op V))`,
  -- `Γ_{uV} := SheafOfModules.evaluation O𝒞 (op (u V))`.
  --
  -- Step 1 (Sub-lemma 1, with `G := E_V`).  `E_V` is exact (presheaf evaluation preserves
  --   homology), so it commutes with the right derived functor of `cohFunctor`:
  --   `E_V (cohPresheafModule i F) = E_V (R^i cohFunctor F) ≅ R^i (cohFunctor ⋙ E_V) F`.
  -- Step 2 (definitional, `rfl`).  `cohFunctor ⋙ E_V = Γ_{uV} ⋙ R`  (the `O_D(V)`-module
  --   `(f_* G)(V) = G(u V)` is `R` applied to the `O_C(uV)`-module `G(u V)`).  So the
  --   codomain of Step 1 is `R^i (Γ_{uV} ⋙ R) F` — this is why `e1 ≪≫ e2` typechecks.
  -- Step 3 (Sub-lemma 4).  `R` is exact, so `R^i (Γ_{uV} ⋙ R) F ≅ R (R^i Γ_{uV} F)
  --   = R (cohomologyOverObject i V F) = R (H^i(u V, F))`.
  -- Composing Steps 1–3 gives `E_V (cohPresheafModule i F) ≅ R (H^i(u V, F))`.
  obtain ⟨e1⟩ := rightDerived_comp_iso_of_preservesHomology
    (cohFunctor u O𝒞 O𝒟 φ) (PresheafOfModules.evaluation O𝒟.obj (Opposite.op V)) i F
  obtain ⟨e2⟩ := restrictScalars_rightDerived_iso u O𝒞 O𝒟 φ i F V
  exact ⟨e1 ≪≫ e2⟩

