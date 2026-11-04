module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteAbComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteDiagFunctor

/-!
# The sheaf of modules of a descent datum on the charts of the members

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X` whose charts are cover dense in the small étale site of `X`, and let `D` be
a descent datum for quasi-coherent modules relative to that family.
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteAbFunctor.lean` assembles
the presheaf of abelian groups of `D` on the site of the charts of the members,
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteCompatibleFamily.lean`
reduces its sheaf condition to unique gluing along the *diagonal* arrows of that site, and
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteDiagonal.lean` proves that
along such an arrow the restriction map of that presheaf is plain restriction inside the component
module.

**This file closes that reduction and carries the datum up to an `𝒪_X`-module.**  The gluing
obligation inside one member is discharged by the sheaf condition of the component module, so the
presheaf of abelian groups of `D` is a **sheaf**; its restriction map is **semilinear**, so with
`CategoryTheory.PresheafOfModules.ofPresheaf` the datum is a **sheaf of modules** on the charts of
the members; and the Comparison Lemma for sheaves of modules then produces an `𝒪_X`-module whose
restriction to those charts is isomorphic to it.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.MemberModLaws`: the semilinearity law a candidate
  presheaf of modules on the charts of the members has to satisfy beyond the three additive laws
  of `AlgebraicGeometry.Space.QuasiCoherentDescent.MemberAbLaws`, with its sections asked for as a
  family of objects of `ModuleCat`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberModOfLaws` and `.memberSheafOfLaws`: the
  presheaf of modules those four laws build, and the sheaf of modules they build together with the
  sheaf condition of the underlying presheaf of abelian groups.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMk`: an isomorphism of descent data
  out of a family of isomorphisms of the component modules commuting with the pairwise
  isomorphisms.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.existsUnique_memberDatumAb_diag`: **the gluing
  obligation inside one member, for the presheaf of abelian groups of a descent datum**, and
  `.isSheaf_memberDatumAbFunctor`: **that presheaf is a sheaf on the charts of the members.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAb_mod_laws`: **the restriction map of
  that presheaf is semilinear**, the one law it needs beyond its three additive ones to be a
  presheaf of modules.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_memberDatumSheaf`: **the sheaf of modules
  of a descent datum on the charts of the members exists**, with the presheaf of abelian groups of
  the datum underlying it on the nose.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_memberRestriction_iso_memberDatumSheaf`:
  **a descent datum comes from an `𝒪_X`-module on the charts of the members.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_of_forall_iso`: a descent datum
  is effective as soon as its component modules are the inverse images of one quasi-coherent
  module compatibly with the pairwise isomorphisms, and
  `.essSurj_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective`,
  `.isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering_of_essSurj`: the canonical
  descent functor of a Zariski covering is an equivalence as soon as every descent datum relative
  to the family is effective.

## What is not proved here

The effectivity clause of Stacks 04W6 itself.  What is still owed is the comparison of the
`𝒪_X`-module `.exists_memberRestriction_iso_memberDatumSheaf` produces with the datum: its
quasi-coherence, and the family of isomorphisms of the component modules with its inverse images
together with their compatibility, which is what
`.isEtaleEffective_of_forall_iso` asks for.  No `@[stacks]` attribute is carried.

## Implementation notes

The discipline the upstream files record applies here unchanged, and two points of it are used
throughout.

**Everything about the presheaf of a descent datum is routed through a declaration at variables.**
`.map_eq_map_of_compatible` is the definition of
`CategoryTheory.Presieve.FamilyOfElements.Compatible` and nothing else; it is stated because
*matching* the conclusion of that definition against a goal spelled at the presheaf of a descent
datum exhausts the recursion depth, while instantiating the same statement at that presheaf is a
first-order assignment.  The same reason puts the whole assembly of
the presheaf of modules -- `.MemberModLaws`, `.memberModOfLaws`, `.memberSheafOfLaws` -- at
variables, with the sections a family of objects of `ModuleCat` so that no module instance has to
be reconciled.

**The transported family of sections is an inline lambda and the sheaf of modules is an
existential.**  The crossing between the sections of the presheaf over a chart of a member and the
sections of the component module over that chart is affordable in a `theorem` and not as the type
of a `def`; so the family a compatible family on a sieve of the charts of the members restricts to
is written out where it is used and never named, and the sheaf of modules of the datum is produced
by an existence statement, which costs nothing because every statement downstream of it is a
`Prop`.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

/-- **A scalar multiple, through the direct-application coercion, with the two arguments carried
as variables.**  The companion of
`AlgebraicGeometry.Space.QuasiCoherentDescent.val_app_apply_add` for the scalar action, and for
the same reason: at a consumer the argument is the value of the restriction factor of a
restriction map, whose type is the sections of a module over a composite chart while this factor
expects the sections of an étale restriction, and those two spellings may meet only in the
position of a function argument -- which is where `z` puts the crossing. -/
theorem val_app_apply_smul {R₁ : Type u} [Ring R₁] {P Q : ModuleCat.{u} R₁} (T : P ⟶ Q)
    (r : R₁) (z x : P) (hz : z = r • x) : T z = r • T x := by
  subst hz
  exact map_smul _ r x

/-- **A function agreeing with a semilinear morphism of modules on two sections is semilinear at
them.**  The function and the morphism are carried separately, and their agreement at the two
sections is a hypothesis, so that the function may have the **target module in another spelling**
than the morphism does: this is the crossing between the sections of an étale restriction and the
sections over a composite chart, and it is paid in the two hypotheses, where both sides are
written out. -/
theorem smul_eq_of_eq_hom {R₀ R₁ : Type u} [Ring R₀] [Ring R₁] (φ : R₀ →+* R₁)
    {M : ModuleCat.{u} R₀} {N : ModuleCat.{u} R₁}
    (A : M ⟶ (ModuleCat.restrictScalars φ).obj N) (F : ↥M → ↥N) (r : R₀) (m : ↥M)
    (hF₁ : F (r • m) = ModuleCat.Hom.hom A (r • m))
    (hF₂ : F m = ModuleCat.Hom.hom A m) :
    F (r • m) = φ r • F m :=
  hF₁.trans ((map_smul (ModuleCat.Hom.hom A) r m).trans
    (congrArg (fun y => φ r • y) hF₂.symm))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- **A square of two isomorphisms and two isomorphisms commutes for the inverses when it
commutes for the forward maps.**  This is the naturality of the inverse of an isomorphism, in the
shape the compatibility field of a morphism of descent data is stated at. -/
theorem inv_naturality {C : Type*} [Category C] {W₁ W₂ Z₁ Z₂ : C} (a₁ : W₁ ≅ W₂) (a₂ : Z₁ ≅ Z₂)
    (d : W₁ ⟶ Z₁) (e : W₂ ⟶ Z₂) (h : a₁.hom ≫ e = d ≫ a₂.hom) :
    a₁.inv ≫ d = e ≫ a₂.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact h.symm

/-- **AN ISOMORPHISM OF DESCENT DATA OUT OF A FAMILY OF ISOMORPHISMS OF THE COMPONENT MODULES
COMMUTING WITH THE PAIRWISE ISOMORPHISMS.**  The forward morphism is the family itself, with the
given compatibility; the inverse is the family of inverses, whose compatibility is
`.inv_naturality` after the inverse images of the two component isomorphisms are read as
isomorphisms (`CategoryTheory.Functor.mapIso`); and the two round trips are those of the
component isomorphisms, by `.DescentDatum.Hom.ext`. -/
def DescentDatum.isoMk {D E : DescentDatum B S hS Yi f} (θ : ∀ i, D.F i ≅ E.F i)
    (hθ : ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom ≫
        (E.transition i j).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom) :
    D ≅ E where
  hom := DescentDatum.Hom.mk (fun i => (θ i).hom) hθ
  inv := DescentDatum.Hom.mk (fun i => (θ i).inv) fun i j =>
    inv_naturality ((modulePullback B S hS (pairFst B S hS Yi f i j)).mapIso (θ i))
      ((modulePullback B S hS (pairSnd B S hS Yi f i j)).mapIso (θ j))
      (D.transition i j).hom (E.transition i j).hom (hθ i j)
  hom_inv_id := DescentDatum.Hom.ext fun i => (θ i).hom_inv_id
  inv_hom_id := DescentDatum.Hom.ext fun i => (θ i).inv_hom_id

/-- The forward morphism of `.DescentDatum.isoMk` is the given family. -/
@[simp]
theorem DescentDatum.isoMk_hom_app {D E : DescentDatum B S hS Yi f} (θ : ∀ i, D.F i ≅ E.F i)
    (hθ : ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom ≫
        (E.transition i j).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom) (i : I) :
    (DescentDatum.isoMk B S hS Yi f θ hθ).hom.app i = (θ i).hom :=
  rfl

/-- **The compatibility of a family of elements on a sieve of the site of the charts of the
members, read at two arrows of the site**, with the presheaf, the sieve and the four arrows all
variables.  It is the definition of
`CategoryTheory.Presieve.FamilyOfElements.Compatible` and nothing else, and it is stated because
the instantiation of a variable is a first-order assignment while *matching* the conclusion of
the definition against a goal spelled at the presheaf of a descent datum is an
exhaustion of the recursion depth: the restriction map of that presheaf is the term being
traversed. -/
theorem map_eq_map_of_compatible (P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ Type w)
    (p : MemberSite B S hS Yi f hf) (T : Sieve p)
    (x : Presieve.FamilyOfElements P T.arrows) (hx : x.Compatible)
    {q r s : MemberSite B S hS Yi f hf} (g₁ : s ⟶ q) (g₂ : s ⟶ r) (k₁ : q ⟶ p) (k₂ : r ⟶ p)
    (h₁ : T.arrows k₁) (h₂ : T.arrows k₂) (hcomp : g₁ ≫ k₁ = g₂ ≫ k₂) :
    P.map g₁.op (x k₁ h₁) = P.map g₂.op (x k₂ h₂) :=
  hx g₁ g₂ h₁ h₂ hcomp

/-! ### Effectivity, and the equivalence, from a family of isomorphisms -/

/-- **A DESCENT DATUM OF AN ÉTALE FAMILY IS EFFECTIVE AS SOON AS ITS COMPONENT MODULES ARE THE
INVERSE IMAGES OF ONE QUASI-COHERENT MODULE, COMPATIBLY WITH THE PAIRWISE ISOMORPHISMS.**  This
is `.DescentDatum.isoMk` at the canonical descent datum of that module. -/
theorem isEtaleEffective_of_forall_iso (D : DescentDatum B S hS Yi f)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (θ : ∀ i, D.F i ≅ (etaleCanonicalDescentDatum B S hS Yi f hf M hM).F i)
    (hθ : ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom ≫
        ((etaleCanonicalDescentDatum B S hS Yi f hf M hM).transition i j).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom) :
    IsEtaleEffective B S hS Yi f hf D :=
  ⟨M, hM, ⟨DescentDatum.isoMk B S hS Yi f θ hθ⟩⟩

/-- **THE CANONICAL DESCENT FUNCTOR OF AN ÉTALE FAMILY IS ESSENTIALLY SURJECTIVE AS SOON AS EVERY
DESCENT DATUM RELATIVE TO THAT FAMILY IS EFFECTIVE.**  The converse of
`AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_of_essSurj`, by
`.isEtaleEffective_iff_essImage`. -/
theorem essSurj_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective
    (h : ∀ D : DescentDatum B S hS Yi f, IsEtaleEffective B S hS Yi f hf D) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).EssSurj where
  mem_essImage D := (isEtaleEffective_iff_essImage B S hS Yi f hf D).1 (h D)

/-- **STACKS 04W6 FOR A ZARISKI COVERING OF AN ALGEBRAIC SPACE, GIVEN THE EFFECTIVITY CLAUSE: the
canonical descent functor of a Zariski covering is an equivalence.**  Faithfulness and fullness
are `.fullyFaithfulEtaleCanonicalDescentFunctorOfIsZariskiCovering`, whose coherence hypothesis is
discharged here by `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction`, which this
development proves unconditionally; so this statement needs no hypothesis beyond the covering.
Essential surjectivity is the hypothesis, and
`.essSurj_etaleCanonicalDescentFunctor_of_forall_isEtaleEffective` is the form in which the
effectivity clause supplies it. -/
theorem isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering_of_essSurj
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom))
    (hess : (etaleCanonicalDescentFunctor B S hS Yi f hf).EssSurj) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).IsEquivalence :=
  ⟨(fullyFaithfulEtaleCanonicalDescentFunctorOfIsZariskiCovering B S hS Yi f hf
      (AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction B S hS) hcov).faithful,
    (fullyFaithfulEtaleCanonicalDescentFunctorOfIsZariskiCovering B S hS Yi f hf
      (AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction B S hS) hcov).full,
    hess⟩

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-! ### A presheaf of modules on the charts of the members, out of one further law -/

/-- **The semilinearity law of a candidate presheaf of modules on the site of the charts of the
members**: each restriction map carries a scalar multiple to the multiple by the restricted
scalar.  The sections are asked for as a family of **objects of `ModuleCat`** over the structure
ring of the charts of the members, so that their additive group and their module structure are
the ones those objects carry and no instance has to be reconciled; that is the shape the sections
of a descent datum present themselves in, by the ascription of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumObj`.

Bundled, and with everything in sight a variable, for the reason recorded at
`AlgebraicGeometry.Space.QuasiCoherentDescent.AddMonoidHomLaws`: the scalar action on the sections
of a descent datum may not be spelled in a statement a consumer writes. -/
structure MemberModLaws
    (obj : ∀ p : (MemberSite B S hS Yi f hf)ᵒᵖ,
      ModuleCat.{u} ((memberRing B S hS Yi f hf).obj.obj p))
    (Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (↥(obj p) → ↥(obj q))) : Prop where
  /-- Each restriction map is semilinear over the restriction map of the structure sheaf. -/
  map_smul : ∀ (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (r : (memberRing B S hS Yi f hf).obj.obj p) (m : ↥(obj p)),
    Fn p q g (r • m) = ((memberRing B S hS Yi f hf).obj.map g).hom r • Fn p q g m

/-- **A presheaf of modules on the site of the charts of the members out of the four laws of its
restriction map**: the three of
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberAbLaws`, which build the underlying presheaf
of abelian groups, and the semilinearity of `.MemberModLaws`.

`CategoryTheory.PresheafOfModules.ofPresheaf` asks for the module structure on the sections as an
instance; it is supplied by hand, because instance search does not unfold the sections of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLawsV` down to the `ModuleCat` object
they are `AddCommGrpCat.of` of.  Everything here is a variable, so a consumer instantiates the
whole assembly by first-order assignment. -/
def memberModOfLaws
    {obj : ∀ p : (MemberSite B S hS Yi f hf)ᵒᵖ,
      ModuleCat.{u} ((memberRing B S hS Yi f hf).obj.obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (↥(obj p) → ↥(obj q))}
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(obj p)) (fun _ => inferInstance) Fn)
    (hM : MemberModLaws B S hS Yi f hf obj Fn) :
    PresheafOfModules.{u} (memberRing B S hS Yi f hf).obj :=
  @PresheafOfModules.ofPresheaf _ _ _ (memberFunctorOfLawsV B S hS Yi f hf hL)
    (fun p => inferInstanceAs (Module ((memberRing B S hS Yi f hf).obj.obj p) ↥(obj p)))
    fun {p q} g r m => hM.map_smul p q g r m

/-- The underlying presheaf of abelian groups of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberModOfLaws` is the presheaf of abelian groups
the three additive laws build, on the nose. -/
theorem memberModOfLaws_presheaf
    {obj : ∀ p : (MemberSite B S hS Yi f hf)ᵒᵖ,
      ModuleCat.{u} ((memberRing B S hS Yi f hf).obj.obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (↥(obj p) → ↥(obj q))}
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(obj p)) (fun _ => inferInstance) Fn)
    (hM : MemberModLaws B S hS Yi f hf obj Fn) :
    (memberModOfLaws B S hS Yi f hf hL hM).presheaf =
      memberFunctorOfLawsV B S hS Yi f hf hL :=
  rfl

/-- **A sheaf of modules on the site of the charts of the members out of the four laws of its
restriction map and the sheaf condition of the underlying presheaf of abelian groups.**  The
sheaf condition is the one of `.memberModOfLaws_presheaf`, so nothing is transported. -/
def memberSheafOfLaws
    {obj : ∀ p : (MemberSite B S hS Yi f hf)ᵒᵖ,
      ModuleCat.{u} ((memberRing B S hS Yi f hf).obj.obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (↥(obj p) → ↥(obj q))}
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(obj p)) (fun _ => inferInstance) Fn)
    (hM : MemberModLaws B S hS Yi f hf obj Fn)
    (hsh : Presheaf.IsSheaf (memberTopology B S hS Yi f hf)
      (memberFunctorOfLawsV B S hS Yi f hf hL)) :
    SheafOfModules.{u} (memberRing B S hS Yi f hf) where
  val := memberModOfLaws B S hS Yi f hf hL hM
  isSheaf := hsh

/-- The underlying presheaf of abelian groups of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberSheafOfLaws`. -/
theorem memberSheafOfLaws_val_presheaf
    {obj : ∀ p : (MemberSite B S hS Yi f hf)ᵒᵖ,
      ModuleCat.{u} ((memberRing B S hS Yi f hf).obj.obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (↥(obj p) → ↥(obj q))}
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(obj p)) (fun _ => inferInstance) Fn)
    (hM : MemberModLaws B S hS Yi f hf obj Fn)
    (hsh : Presheaf.IsSheaf (memberTopology B S hS Yi f hf)
      (memberFunctorOfLawsV B S hS Yi f hf hL)) :
    (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.presheaf =
      memberFunctorOfLawsV B S hS Yi f hf hL :=
  rfl

variable (D : DescentDatum B S hS Yi f)
  (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
    (fun _ => inferInstance)
    (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))

/-- **THE RESTRICTION MAP OF THE PRESHEAF OF ABELIAN GROUPS OF A DESCENT DATUM IS SEMILINEAR**
over the restriction map of the structure sheaf of the charts of the members, which is the one
law a presheaf of abelian groups needs beyond its three additive ones to be a presheaf of
modules.

Both factors supply it: the restriction factor is semilinear over the restriction of the
structure sheaf along the morphism of charts the arrow of the site induces -- which is that of
the structure sheaf of `X` along the arrow itself -- and the transition factor is linear.  The
crossing between the sections of the étale restriction and the sections over the composite chart
is paid in the two hypotheses of `.smul_eq_of_eq_hom`, at
`.memberDatumAbRestrFn_apply_of_eq`, and the crossing between the two spellings of the scalar is
paid in the argument of `.val_app_apply_smul`. -/
theorem memberDatumAb_mod_laws :
    MemberModLaws B S hS Yi f hf (memberDatumObj B S hS Yi f hf D)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)) where
  map_smul p q g r m :=
    val_app_apply_smul _ (((memberRing B S hS Yi f hf).obj.map g).hom r) _ _
      (smul_eq_of_eq_hom ((memberRing B S hS Yi f hf).obj.map g).hom _
        (memberDatumAbRestrFn B S hS Yi f hf D p q g) r m
        (memberDatumAbRestrFn_apply_of_eq B S hS Yi f hf D p q g (r • m) (r • m) rfl)
        (memberDatumAbRestrFn_apply_of_eq B S hS Yi f hf D p q g m m rfl))

/-- **The family of sections of the component module a compatible family on a sieve of the charts
of the members restricts to is compatible.**  The family is the given one read at the diagonal
arrows, with nothing transported: along a diagonal arrow the restriction map of the presheaf of
abelian groups of the datum is plain restriction inside `D.F i`
(`.memberDatumAbFunctor_coyoneda_map_memberDiagHom`), and two morphisms of charts of `Y i` with a
common composite still have one when read as arrows of the site
(`.memberDiagHom_comp_congr`). -/
theorem compatible_memberDatumAbDiag_pre (E : AddCommGrpCat.{u}) (i : I)
    (V : SmallEtale B S hS (Yi i).1) (T : Sieve (memberPair B S hS Yi f hf i V))
    (x : Presieve.FamilyOfElements
      (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)) T.arrows)
    (hx : x.Compatible) {Z Y₁ Y₂ : SmallEtale B S hS (Yi i).1} (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂)
    (a₁ : Y₁ ⟶ V) (a₂ : Y₂ ⟶ V)
    (h₁ : T.arrows (memberDiagHom B S hS Yi f hf a₁))
    (h₂ : T.arrows (memberDiagHom B S hS Yi f hf a₂)) (hcomp : g₁ ≫ a₁ = g₂ ≫ a₂) :
    (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).map
        (memberDiagHom B S hS Yi f hf g₁).op (x (memberDiagHom B S hS Yi f hf a₁) h₁) =
      (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).map
        (memberDiagHom B S hS Yi f hf g₂).op (x (memberDiagHom B S hS Yi f hf a₂) h₂) :=
  map_eq_map_of_compatible B S hS Yi f hf _ _ T x hx (memberDiagHom B S hS Yi f hf g₁)
    (memberDiagHom B S hS Yi f hf g₂) (memberDiagHom B S hS Yi f hf a₁)
    (memberDiagHom B S hS Yi f hf a₂) h₁ h₂
    (memberDiagHom_comp_congr B S hS Yi f hf g₁ g₂ a₁ a₂ hcomp)

/-- A compatible family `x` of sections of the presheaf of abelian groups of the datum on a sieve
`T` of the object `(i, V)` of the site of the charts of the members, read at the diagonal arrows
`memberDiagHom a`, is a compatible family of sections of `D.F i` on `memberDiagSieve V T`. -/
theorem compatible_memberDatumAbDiagFamily (E : AddCommGrpCat.{u}) (i : I)
    (V : SmallEtale B S hS (Yi i).1) (T : Sieve (memberPair B S hS Yi f hf i V))
    (x : Presieve.FamilyOfElements
      (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)) T.arrows)
    (hx : x.Compatible) :
    Presieve.FamilyOfElements.Compatible
      (P := (D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E))
      (R := (memberDiagSieve B S hS Yi f hf V T).arrows)
      (fun _ a ha => x (memberDiagHom B S hS Yi f hf a) ha) := by
  intro Y₁ Y₂ Z g₁ g₂ a₁ a₂ h₁ h₂ hcomp
  exact ((memberDatumAbFunctor_coyoneda_map_memberDiagHom B S hS Yi f hf D hL E g₁
        (x (memberDiagHom B S hS Yi f hf a₁) h₁)).symm.trans
      (compatible_memberDatumAbDiag_pre B S hS Yi f hf D hL E i V T x hx g₁ g₂ a₁ a₂ h₁ h₂
        hcomp)).trans
    (memberDatumAbFunctor_coyoneda_map_memberDiagHom B S hS Yi f hf D hL E g₂
      (x (memberDiagHom B S hS Yi f hf a₂) h₂))

/-- **The gluing obligation inside one member, for the presheaf of abelian groups of a descent
datum.**  A compatible family of sections of that presheaf on a covering sieve of an object
`(i, V)` of the site of the charts of the members has a unique section restricting correctly along
the morphisms of charts of `Y i` in that sieve.

The transported family is an inline lambda: the family of sections of the presheaf indexed by the
morphisms of charts of `Y i` in the sieve *is* a family of sections of `D.F i` indexed by the part
of the sieve living inside the member, its compatibility is
`.compatible_memberDatumAbDiagFamily`, and the gluing is the sheaf condition of `D.F i`
(`.exists_unique_isAmalgamation_memberDiagSieve`). -/
theorem existsUnique_memberDatumAb_diag (E : AddCommGrpCat.{u}) (i : I)
    (V : SmallEtale B S hS (Yi i).1) (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V)))
    (x : Presieve.FamilyOfElements
      (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)) T.arrows)
    (hx : x.Compatible) :
    ∃! t : (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).obj
        (Opposite.op (memberPair B S hS Yi f hf i V)),
      ∀ {W : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
        (ha : T.arrows (memberDiagHom B S hS Yi f hf a)),
        (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).map
            (memberDiagHom B S hS Yi f hf a).op t =
          x (memberDiagHom B S hS Yi f hf a) ha := by
  obtain ⟨t, ht, hu⟩ :=
    exists_unique_isAmalgamation_memberDiagSieve B S hS Yi f hf ((D.F i).isSheaf E) T hT
      (fun _ a ha => x (memberDiagHom B S hS Yi f hf a) ha)
      (compatible_memberDatumAbDiagFamily B S hS Yi f hf D hL E i V T x hx)
  refine ⟨t, ?_, ?_⟩
  · intro W a ha
    exact (memberDatumAbFunctor_coyoneda_map_memberDiagHom B S hS Yi f hf D hL E a t).trans
      (ht a ha)
  · intro y hy
    refine hu y ?_
    intro W a ha
    exact (memberDatumAbFunctor_coyoneda_map_memberDiagHom B S hS Yi f hf D hL E a y).symm.trans
      (hy a ha)

/-- **THE PRESHEAF OF ABELIAN GROUPS OF A DESCENT DATUM ON THE CHARTS OF THE MEMBERS IS A
SHEAF**, with the three laws of its restriction map carried as a hypothesis.  This is
`.isSheaf_memberTopology_of_memberDiagHom` — the sheaf condition on the whole site reduced to the
gluing obligation inside one member — fed with `.existsUnique_memberDatumAb_diag`, which is that
obligation discharged by the sheaf condition of the component module. -/
theorem isSheaf_memberDatumAbFunctor :
    Presheaf.IsSheaf (memberTopology B S hS Yi f hf)
      (memberFunctorOfLawsV B S hS Yi f hf hL) :=
  isSheaf_memberTopology_of_memberDiagHom B S hS Yi f hf
    (memberFunctorOfLawsV B S hS Yi f hf hL)
    fun E i V T hT x hx => existsUnique_memberDatumAb_diag B S hS Yi f hf D hL E i V T hT x hx

/-- **THE SHEAF OF MODULES OF A DESCENT DATUM ON THE CHARTS OF THE MEMBERS EXISTS**, and its
underlying presheaf of abelian groups is the presheaf of abelian groups of the datum on the nose.

The four laws are `.memberDatumAb_laws` and `.memberDatumAb_mod_laws`, the sheaf condition is
`.isSheaf_memberDatumAbFunctor`, and the assembly is `.memberSheafOfLaws`; the identification of
the underlying presheaf of abelian groups is
`CategoryTheory.PresheafOfModules.ofPresheaf_presheaf`, so nothing is transported.

An **existence statement** and not a `def`: naming this sheaf would put the restriction map of the
presheaf of the datum in the body of a `def`, which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteAbFunctor.lean` record as a
deterministic timeout of the kernel in every shape.  Nothing is lost: every statement
downstream of it is a `Prop`, so a consumer obtains the sheaf inside its own proof. -/
theorem exists_memberDatumSheaf :
    ∃ N : SheafOfModules.{u} (memberRing B S hS Yi f hf),
      N.val.presheaf = memberFunctorOfLawsV B S hS Yi f hf
        (memberDatumAb_laws B S hS Yi f hf D) :=
  ⟨memberSheafOfLaws B S hS Yi f hf (memberDatumAb_laws B S hS Yi f hf D)
      (memberDatumAb_mod_laws B S hS Yi f hf D)
      (isSheaf_memberDatumAbFunctor B S hS Yi f hf D (memberDatumAb_laws B S hS Yi f hf D)),
    memberSheafOfLaws_val_presheaf B S hS Yi f hf _ _ _⟩

/-- **A DESCENT DATUM COMES FROM AN `𝒪_X`-MODULE ON THE CHARTS OF THE MEMBERS**: there is an
`𝒪_X`-module whose restriction to the site of the charts of the members is isomorphic to the
sheaf of modules of the datum.

`.exists_memberDatumSheaf` supplies that sheaf of modules and
`AlgebraicGeometry.Space.QuasiCoherentDescent.essSurj_memberRestriction_anyIndex` -- the
Comparison Lemma
for sheaves of modules on the charts of the members -- supplies the module.  Neither
quasi-coherence of the module nor the isomorphism of the datum with its canonical descent datum is
asserted here. -/
theorem exists_memberRestriction_iso_memberDatumSheaf :
    ∃ (M : Modules.{u, u} B S hS X.1 X.2) (N : SheafOfModules.{u} (memberRing B S hS Yi f hf)),
      N.val.presheaf = memberFunctorOfLawsV B S hS Yi f hf
          (memberDatumAb_laws B S hS Yi f hf D) ∧
        Nonempty ((memberRestriction B S hS Yi f hf).obj M ≅ N) := by
  obtain ⟨N, hN⟩ := exists_memberDatumSheaf B S hS Yi f hf D
  obtain ⟨M, he⟩ := (essSurj_memberRestriction_anyIndex B S hS Yi f hf).mem_essImage N
  exact ⟨M, N, hN, he⟩

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
