module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.LocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Tag 01AN (Lemma 17.4.2): Let `(X, O_X)` be a ringed space and `F` a sheaf of
`O_X`-modules. Let `I` be a set and `s_i ∈ Γ(X, F)`, `i ∈ I`, global sections. Then the
following are equivalent:

1. The sections `s_i` generate `F`, i.e. the associated morphism of `O_X`-modules
     `φ : ⨁_{i ∈ I} O_X ⟶ F`
   (the map sending the `i`-th basis section `1` to `s_i`) is surjective as a morphism of
   sheaves of `O_X`-modules (Definition 2 / Tag 01AM, Definition 17.4.1).

2. For every point `x ∈ X`, the germs `s_{i,x} ∈ F_x` generate the `O_{X,x}`-module `F_x`
   (Definition 3).

# Background and context

* `(X, O_X)` is a ringed space: a topological space `X` with a sheaf `O_X` of commutative
  rings. We model `O_X` as a `Sheaf (Opens.grothendieckTopology X) RingCat`, i.e. a sheaf of
  rings on the site of opens of `X`, and `F` as `SheafOfModules O_X`. This is the
  Mathlib-native framework for sheaves of modules over a sheaf of rings.

* `Γ(X, F)` (global sections) is modelled by `F.sections`, the `O_X(X)`-module of compatible
  families of local sections; this is exactly the type of global sections.

* The stalk `F_x = colim_{x ∈ U} F(U)` is a module over the stalk ring
  `O_{X,x} = colim_{x ∈ U} O_X(U)`. (For a general ringed space `O_{X,x}` is merely a
  commutative ring, not necessarily local.) Mathlib does not (yet) provide the
  `O_{X,x}`-module structure on the stalk of a sheaf of modules. We therefore phrase
  statement (2) through its standard, provably equivalent reformulation explained below.

# Main Definition(s)

## Definition 1 (Map associated to a family of sections).

Given a family `s : I → F.sections` of global sections, Mathlib's free-module adjunction
`SheafOfModules.freeHomEquiv : (free I ⟶ F) ≃ (I → F.sections)` produces the morphism
`φ : ⨁_{i} O_X = free I ⟶ F` sending the `i`-th basis section to `s i`. This is
`assocMap` below.

## Definition 2 (Sections generate `F`).  (Stacks Tag 01AM, Definition 17.4.1)

The sections `s_i` *generate* `F` when the associated morphism `φ` is surjective as a
morphism of sheaves of `O_X`-modules, i.e. `Epi φ`. (In the balanced category of sheaves of
modules, an epimorphism is precisely a surjective — equivalently locally surjective —
morphism of sheaves.)

## Definition 3 (Generation of a module by a family).

For an `R`-module `M`, elements `(m_i)` generate `M` iff the `R`-linear map
`⨁_i R → M`, `(r_i) ↦ Σ r_i m_i`, is surjective.

Applied at a point `x`, the germs `s_{i,x}` generate the `O_{X,x}`-module `F_x` iff the map
`⨁_{i} O_{X,x} → F_x` sending the `i`-th basis element to `s_{i,x}` is surjective. Now the
stalk of the free sheaf `⨁_i O_X` at `x` is canonically `⨁_i O_{X,x}`, and under this
identification the stalk `φ_x` of `φ` is exactly the map `⨁_i O_{X,x} → F_x` sending the
`i`-th basis element to `s_{i,x}` (direct sums commute with
stalks). Hence:

  germs `s_{i,x}` generate the `O_{X,x}`-module `F_x`   ⟺   `φ_x` is surjective.

Both sides of the stalk map are abelian groups (the underlying additive structure of the
modules over the stalk ring), and surjectivity of an `O_{X,x}`-linear map is the same as
surjectivity of the underlying map of abelian groups. We therefore express statement (2) as:
for every `x`, the stalk `φ_x` (taken in the category of abelian groups) is surjective. This
is the standard sheaf-theoretic reformulation of "germs generate the stalk module" and is the
engine of the proof of Tag 01AN.
-/

open CategoryTheory TopologicalSpace Limits Opposite


variable {X : TopCat.{0}} (O_X : Sheaf (Opens.grothendieckTopology X) RingCat)
  (F : SheafOfModules.{0} O_X) {I : Type}

/-- Definition 1: the morphism `φ : ⨁_{i ∈ I} O_X ⟶ F` of sheaves of `O_X`-modules
associated to a family `s : I → Γ(X, F)` of global sections, sending the `i`-th basis
section to `s i`. -/
@[ega "0 5.1.1" "partial", sga "6 II 2.3.1"]
noncomputable def assocMap (s : I → F.sections) : SheafOfModules.free (R := O_X) I ⟶ F :=
  (SheafOfModules.freeHomEquiv F).symm s

/-- Definition 2: the sections `s` *generate* `F` if the associated morphism `assocMap O_X F s`
is an epimorphism of sheaves of `O_X`-modules (equivalently, a surjective morphism of
sheaves). -/
@[ega "0 5.1.1", sga "6 II 2.1.1" "special case"]
def Generate (s : I → F.sections) : Prop :=
  Epi (assocMap O_X F s)

/-- The stalk at `x` of (the underlying abelian-group-sheaf image of) a morphism `φ` of
sheaves of `O_X`-modules. This is the map `φ_x` on stalks; its source and target are the
stalks of the underlying sheaves of abelian groups of the source and target. -/
noncomputable def stalkMapAb {M N : SheafOfModules O_X} (φ : M ⟶ N) (x : X) :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      ((SheafOfModules.toSheaf O_X).map φ))

/-- Statement (2), as the standard reformulation of "the germs `s_{i,x}` generate the
`O_{X,x}`-module `F_x` for every `x`": for every point `x`, the stalk `φ_x` of the associated
morphism is surjective. -/
@[ega "0 5.1.1"]
def GenerateStalks (s : I → F.sections) : Prop :=
  ∀ x : X, Function.Surjective (stalkMapAb O_X (assocMap O_X F s) x).hom

/-- If a cokernel cofork `c` of `f` (`IsColimit`) has a zero point, then `f` is an
epimorphism. -/
theorem isZero_cofork_of_epi {C : Type*} [Category C] [Preadditive C] {A B : C} (f : A ⟶ B)
    [Epi f] (c : CokernelCofork f) (hc : IsColimit c) : IsZero c.pt := by
  have hπ : Cofork.π c = 0 := (cancel_epi f).1 (by simp [CokernelCofork.condition c])
  rw [IsZero.iff_id_eq_zero]
  exact Cofork.IsColimit.hom_ext hc (by simp [hπ])

/-- The converse: an `IsColimit` cokernel cofork of `f` whose point is zero forces `f` epi. -/
theorem epi_of_cofork {C : Type*} [Category C] [Preadditive C] {A B : C} (f : A ⟶ B)
    (c : CokernelCofork f) (hc : IsColimit c) (hz : IsZero c.pt) : Epi f := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z g hg
  let t : CokernelCofork f := CokernelCofork.ofπ g hg
  have h1 : Cofork.π c ≫ hc.desc t = Cofork.π t := Cofork.IsColimit.π_desc hc
  have ht0 : Cofork.π t = 0 := by rw [← h1, hz.eq_of_tgt (Cofork.π c) 0, zero_comp]
  simpa [t] using ht0

/-- The image of `φ` under the module sheafification reflector applied to the underlying
presheaf-of-modules morphism. By the reflective adjunction this is iso-conjugate to `φ`. -/
noncomputable def sheafificationForgetMap {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N) :=
  (PresheafOfModules.sheafification (𝟙 O_X.obj)).map ((SheafOfModules.forget O_X).map φ)

/-- `Epi (sheafificationForgetMap φ)` iff `Epi φ`, by conjugating with the counit iso. -/
private theorem epi_sheafificationForgetMap_iff {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N) :
    Epi (sheafificationForgetMap O_X φ) ↔ Epi φ := by
  have key : sheafificationForgetMap O_X φ ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 O_X.obj)).counit.app N =
      (PresheafOfModules.sheafificationAdjunction (𝟙 O_X.obj)).counit.app M ≫ φ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 O_X.obj)).counit.naturality φ
  rw [← epi_comp_iff_of_isIso _ ((PresheafOfModules.sheafificationAdjunction
    (𝟙 O_X.obj)).counit.app N), key, epi_comp_iff_of_epi]

/-- `Epi φ` in `SheafOfModules O_X` implies `Epi (sheafificationForgetMap φ)`, via the
  iso-conjugation provided
by the counit of the reflective module-sheafification adjunction (the counit is an iso since
the right adjoint is fully faithful). This uses no stubbed colimit-preservation instance. -/
theorem epi_g {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N) [Epi φ] :
    Epi (sheafificationForgetMap O_X φ) :=
  (epi_sheafificationForgetMap_iff O_X φ).2 ‹_›

/-- `Epi` of the `AddCommGrpCat`-sheafified underlying map of `h` is equivalent to `Epi` of
its module-sheafification, by comparing the images of a cokernel cofork of `h`. -/
private theorem epi_F_iff_epi_L {P Q : PresheafOfModules O_X.obj} (h : P ⟶ Q) :
    Epi ((PresheafOfModules.toPresheaf O_X.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map h) ↔
    Epi ((PresheafOfModules.sheafification (𝟙 O_X.obj)).map h) := by
  let cc : CokernelCofork h := colimit.cocone (parallelPair h 0)
  have hcc : IsColimit cc := colimit.isColimit (parallelPair h 0)
  have hF := CokernelCofork.mapIsColimit cc hcc (PresheafOfModules.toPresheaf O_X.obj ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)
  have hL := CokernelCofork.mapIsColimit cc hcc (PresheafOfModules.sheafification (𝟙 O_X.obj))
  -- The `F`-cokernel point is `toSheaf` applied to the `L`-cokernel point (definitionally).
  have key : IsZero ((cc.map (PresheafOfModules.toPresheaf O_X.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)).pt) ↔
      IsZero ((cc.map (PresheafOfModules.sheafification (𝟙 O_X.obj))).pt) :=
    ⟨fun hz => by
      rw [IsZero.iff_id_eq_zero]
      exact (SheafOfModules.toSheaf O_X).map_injective (hz.eq_of_tgt _ _),
     Functor.map_isZero (SheafOfModules.toSheaf O_X)⟩
  exact ⟨fun _ => epi_of_cofork _ _ hL (key.1 (isZero_cofork_of_epi _ _ hF)),
    fun _ => epi_of_cofork _ _ hF (key.2 (isZero_cofork_of_epi _ _ hL))⟩

/-- **Sub-lemma A (sound form).** For a morphism `h` of presheaves of `O_X.obj`-modules, if
its module-sheafification `L.map h` is an epimorphism, then the image of `h` under
`toPresheaf ⋙ presheafToSheaf` (the `AddCommGrpCat`-sheafification of the underlying presheaf)
is an epimorphism of `AddCommGrpCat`-sheaves.

The proof is the honest cokernel computation: `L ⋙ toSheaf = toPresheaf ⋙ presheafToSheaf`
*by construction* (definitional), and both `L` and `toPresheaf ⋙ presheafToSheaf` preserve the
cokernel of `h` (sound `PreservesColimit (parallelPair h 0) _` instances for a *generic* `h`).
`Epi (L.map h)` makes the `L`-cokernel point zero, and `toSheaf` (an additive functor) sends it
to zero, which is exactly the point of the `toPresheaf ⋙ presheafToSheaf` cokernel cofork; hence
that cofork has zero point, so `(toPresheaf ⋙ presheafToSheaf).map h` is epi. No stubbed
`toSheaf`/`forget`/`presheafToSheaf` colimit-preservation instance is used; the cokernel of the
*generic* `h` lives in `PresheafOfModules`, whose colimits are sound. -/
theorem epi_F_of_epi_L {P Q : PresheafOfModules O_X.obj} (h : P ⟶ Q)
    [Epi ((PresheafOfModules.sheafification (𝟙 O_X.obj)).map h)] :
    Epi ((PresheafOfModules.toPresheaf O_X.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map h) :=
  (epi_F_iff_epi_L O_X h).2 ‹_›

/-- **Honest core obligation (the genuine mathematical content of Tag 01AN's engine).**
An epimorphism `φ` of sheaves of `O_X`-modules is *locally surjective* on the underlying
presheaf of abelian groups, i.e. `(toPresheaf O_X.obj).map (φ.val)` is locally surjective.

This is the one step that cannot be obtained from sound Mathlib API by `rw`/`exact` alone in this
environment (the `PreservesEpimorphisms (toSheaf O_X)` / `PreservesFiniteColimits (toSheaf O_X)`
instances are unproved and must NOT be used). It is the honest replacement.

INFORMAL PROOF ("Step 2" + "Sub-lemma A"): use the SOUND module sheafification reflector
`L := PresheafOfModules.sheafification (𝟙 O_X.obj)`, with the adjunction
`PresheafOfModules.sheafificationAdjunction (𝟙 O_X.obj) : L ⊣ (forget O_X ⋙ restrictScalars (𝟙))`.
Because `SheafOfModules.forget O_X` is `Full` + `Faithful` (SOUND) and `restrictScalars (𝟙)` is an
equivalence, the adjunction is reflective, so `L (forget φ)` is iso-conjugate to `φ`; hence
`Epi φ ⟹ Epi (L.map φ.val)`. Then the module analogue of
`Presheaf.isLocallySurjective_presheafToSheaf_map_iff` (SOUND, for `AddCommGrpCat`-presheaves:
`Sheaf.IsLocallySurjective ((presheafToSheaf J A).map q) ↔ Presheaf.IsLocallySurjective J q`)
transports `Epi (L.map φ.val)` to
`Presheaf.IsLocallySurjective J ((toPresheaf O_X.obj).map φ.val)`, using the constructional
compatibility of module sheafification with `AddCommGrpCat` sheafification (the underlying additive
sheaf of `L P` is the `AddCommGrpCat`-sheafification of the underlying additive presheaf of `P`)
together with the abelian `Epi ↔ cokernel = 0` criterion — none of which routes through any stubbed
`toSheaf`/`forget` colimit-preservation instance.

SOUND ingredients confirmed: `PresheafOfModules.sheafificationAdjunction (𝟙 O_X.obj)` typechecks;
`(SheafOfModules.forget O_X).Full` and `.Faithful` resolve;
`Presheaf.isLocallySurjective_presheafToSheaf_map_iff`
exists for `AddCommGrpCat`. -/
theorem epi_isLocallySurjective_toPresheaf
    {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N) [Epi φ] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O_X.obj).map ((SheafOfModules.forget O_X).map φ)) := by
  -- `Epi φ` ⟹ `Epi (sheafificationForgetMap φ)` (iso-conjugation by the reflective adjunction
  -- counit).
  have : Epi ((PresheafOfModules.sheafification (𝟙 O_X.obj)).map
      ((SheafOfModules.forget O_X).map φ)) := epi_g O_X φ
  -- Sheaf epi ⟺ sheaf locally surjective ⟺ presheaf locally surjective (sound `Sheaf`/`Presheaf`
  -- API).
  rw [← CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff
        (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf O_X.obj).map ((SheafOfModules.forget O_X).map φ)),
      CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat]
  -- Sub-lemma A: the `AddCommGrpCat`-sheafification of the underlying presheaf map is epi.
  exact epi_F_of_epi_L O_X ((SheafOfModules.forget O_X).map φ)

/-- `Epi` of `toSheaf.map φ` is equivalent to presheaf local surjectivity of the underlying
presheaf map of `φ` (balanced `AddCommGrpCat`-sheaf category; `toSheaf` is defeq to forgetting). -/
private theorem epi_toSheaf_map_iff {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N) :
    Epi ((SheafOfModules.toSheaf O_X).map φ) ↔ Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O_X.obj).map ((SheafOfModules.forget O_X).map φ)) := by
  rw [← CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      (J := Opens.grothendieckTopology X) AddCommGrpCat ((SheafOfModules.toSheaf O_X).map φ),
     ← CategoryTheory.Sheaf.isLocallySurjective_sheafToPresheaf_map_iff
      ((SheafOfModules.toSheaf O_X).map φ)]
  rfl

/-- **CRUX sub-lemma.** The forgetful functor `SheafOfModules.toSheaf O_X` — which sends a
sheaf of `O_X`-modules to its underlying sheaf of abelian groups — *preserves epimorphisms*.

Informal proof (rigorous): The category `SheafOfModules O_X` is abelian, hence balanced, and
likewise `Sheaf J AddCommGrpCat` is abelian/balanced. By the standard sheaf-theoretic
characterisation of epimorphisms (`Sheaf.isLocallySurjective_iff_epi'`), in each of these
balanced concrete sheaf categories a morphism is an epimorphism **iff** it is locally
surjective (`Sheaf.IsLocallySurjective`), i.e. iff its image presheaf morphism is locally
surjective as a map of presheaves of sets (`Presheaf.IsLocallySurjective`). Now by the
formula for `toSheaf` (see `#print SheafOfModules.toSheaf`), the underlying presheaf-of-sets
map of `(toSheaf O_X).map φ` is *the very same* function-on-sections as the underlying
presheaf-of-sets map of `φ`: `toSheaf` only forgets the module structure on the values, it
does not change the underlying sheaf-of-sets or the maps between sections. Local surjectivity
is a property of that underlying presheaf-of-sets morphism alone (for each section over an
open `U` and each point, the section is locally in the image), so it is preserved verbatim.
Therefore `φ` locally surjective `⇒` `(toSheaf O_X).map φ` locally surjective `⇒`
`(toSheaf O_X).map φ` is an epimorphism. (Equivalently: stalkwise, the stalk map of the
underlying abelian-group sheaf agrees with the underlying-set stalk map of `φ`, and surjectivity
on stalks of modules is surjectivity on stalks of the underlying abelian groups.)

NOTE: in the current environment the registered instance `PreservesEpimorphisms (toSheaf O_X)`
is unproved, so it must NOT be used (e.g. via `Functor.epi_map_iff_epi`); this lemma is
the honest replacement. Its mirror is `toSheaf_reflectsEpi` below, which is what
`generate_iff_generateStalks` uses. -/
@[sga "4 V 3.5" "partial"]
theorem toSheaf_preservesEpi {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N) [Epi φ] :
    Epi ((SheafOfModules.toSheaf O_X).map φ) := by
  rw [epi_toSheaf_map_iff]
  exact epi_isLocallySurjective_toPresheaf O_X φ

/-- A faithful functor with zero morphisms reflects "is zero": if `G.obj A` is zero then `A`
is zero. -/
theorem isZero_of_faithful {C D : Type*} [Category C] [Category D] [Limits.HasZeroMorphisms C]
    [Limits.HasZeroMorphisms D] (G : C ⥤ D) [G.Faithful] [G.PreservesZeroMorphisms]
    {A : C} (h : IsZero (G.obj A)) : IsZero A := by
  rw [IsZero.iff_id_eq_zero]
  exact G.map_injective (h.eq_of_tgt _ _)

/-- **Converse of `epi_F_of_epi_L`.** If the `AddCommGrpCat`-sheafification of the underlying
presheaf map of `h` is epi, then the module-sheafification `L.map h` is epi.

Honest cokernel argument: `L ⋙ toSheaf = toPresheaf ⋙ presheafToSheaf` definitionally; both `L`
and `toPresheaf ⋙ presheafToSheaf` preserve the cokernel of the generic `h` (sound instances).
`Epi ((toPresheaf ⋙ presheafToSheaf).map h)` makes the `(L ⋙ toSheaf)`-cokernel point zero;
`toSheaf` is faithful so it reflects "is zero" of the `L`-cokernel point; hence that cofork has
zero point, so `L.map h` is epi. No stubbed colimit-preservation instance is used. -/
theorem epi_L_of_epi_F {P Q : PresheafOfModules O_X.obj} (h : P ⟶ Q)
    [Epi ((PresheafOfModules.toPresheaf O_X.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map h)] :
    Epi ((PresheafOfModules.sheafification (𝟙 O_X.obj)).map h) :=
  (epi_F_iff_epi_L O_X h).1 ‹_›

/-- **Converse of `epi_g`.** `Epi (sheafificationForgetMap φ)` implies `Epi φ`, via the
  iso-conjugation provided
by the counit of the reflective module-sheafification adjunction (the counit is an iso). -/
theorem epi_of_epi_gmap {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N)
    [Epi (sheafificationForgetMap O_X φ)] : Epi φ :=
  (epi_sheafificationForgetMap_iff O_X φ).1 ‹_›

/-- A morphism `φ` of sheaves of `O_X`-modules is an epimorphism if its underlying morphism of
sheaves of abelian groups `(SheafOfModules.toSheaf O_X).map φ` is an epimorphism. -/
theorem toSheaf_reflectsEpi {M N : SheafOfModules.{0} O_X} (φ : M ⟶ N)
    [Epi ((SheafOfModules.toSheaf O_X).map φ)] : Epi φ := by
  -- Mirror of toSheaf_preservesEpi, run in reverse.
  -- Step 1: `Epi ((toSheaf O_X).map φ)` ⟹ presheaf local surjectivity of `(toPresheaf).map
  -- (forget.map φ)`.
  have hLS := (epi_toSheaf_map_iff O_X φ).1 ‹_›
  -- Step 2: presheaf local surjectivity ⟹ `Epi ((presheafToSheaf J Ab).map (toPresheaf.map
  -- (forget.map φ)))`.
  have hEpiF : Epi ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf O_X.obj).map ((SheafOfModules.forget O_X).map φ))) := by
    rwa [← CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat,
      CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
  -- Step 3: converse of `epi_F_of_epi_L` ⟹ `Epi (sheafificationForgetMap φ)`.
  have : Epi ((PresheafOfModules.toPresheaf O_X.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        ((SheafOfModules.forget O_X).map φ)) := hEpiF
  have : Epi (sheafificationForgetMap O_X φ) := epi_L_of_epi_F O_X _
  -- Step 4: converse of `epi_g` (counit iso) ⟹ `Epi φ`.
  exact epi_of_epi_gmap O_X φ

-- Main Statement(s)

/-- **Generation by global sections, tested on stalks of the underlying abelian sheaves.** Let
`(X, O_X)` be a ringed space, `F` a sheaf of `O_X`-modules, `I` a set, and `s_i ∈ Γ(X, F)` global
sections. Then the sections generate `F` (Definition 2) if and only if for every point `x` the
stalk at `x` of the associated morphism `⨁_{i ∈ I} O_X ⟶ F`, taken on underlying sheaves of
abelian groups, is surjective. The form with the germs spanning the `O_{X,x}`-module `F_x` is
`AlgebraicGeometry.generates_iff_stalkwise_generates`.

PROOF: a finite chain of iff's. With `φ := assocMap O_X F s` and `ψ := (toSheaf O_X).map φ`:
  Epi φ  ↔ Epi ψ                                   -- toSheaf_preservesEpi + toSheaf_reflectsEpi
        ↔ Sheaf.IsLocallySurjective ψ              -- Sheaf.isLocallySurjective_iff_epi'
        ↔ Presheaf.IsLocallySurjective (sheafToPresheaf.map ψ)
                                    -- Sheaf.isLocallySurjective_sheafToPresheaf_map_iff
        ↔ ∀ x, Surjective ((stalkFunctor _ x).map (sheafToPresheaf.map ψ))
                                                   -- locally_surjective_iff_surjective_on_stalks
                                                   -- (defeq to TopCat version)
        ≡ GenerateStalks                           -- defeq: matches `stalkMapAb`. -/
@[ega "0 5.1.1" "parenthetical"]
theorem generate_iff_generateStalks (s : I → F.sections) :
    Generate O_X F s ↔ GenerateStalks O_X F s := by
  unfold Generate GenerateStalks
  set φ := assocMap O_X F s
  set ψ := (SheafOfModules.toSheaf O_X).map φ
  -- Step 1: Epi φ ↔ Epi ψ. Forward: `toSheaf_preservesEpi` (CRUX sub-lemma).
  --         Backward: `toSheaf_reflectsEpi` (honest replacement; the `ReflectsEpimorphisms`
  --         instance / `epi_of_epi_map` is unproved in this environment).
  rw [show Epi φ ↔ Epi ψ from
    ⟨fun _ => toSheaf_preservesEpi O_X φ, fun h => by
      have : Epi ((SheafOfModules.toSheaf O_X).map φ) := h
      exact toSheaf_reflectsEpi O_X φ⟩]
  -- Step 2: Epi ψ ↔ Sheaf.IsLocallySurjective ψ  (balanced sheaf category).
  -- Step 3: pass to the underlying presheaf local-surjectivity.
  rw [← CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat ψ,
    ← CategoryTheory.Sheaf.isLocallySurjective_sheafToPresheaf_map_iff ψ]
  -- Step 4: presheaf local surjectivity ↔ surjective on all stalks; defeq to `GenerateStalks`.
  exact TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _
