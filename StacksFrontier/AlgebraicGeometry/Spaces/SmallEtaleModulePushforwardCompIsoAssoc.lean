module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# Associativity of the composition comparisons of Stacks 03LU, unconditionally

For a composable pair `f : X ⟶ Y`, `g : Y ⟶ Z` of morphisms of algebraic spaces, Stacks 03LU
provides the comparisons `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images and `g^* ∘ f^* ≅ (f ≫ g)^*` of
inverse images of `𝒪`-modules.  For three composable morphisms each comparison can be applied in
two orders, and this file proves that the two agree — for the direct images from the cocycle law
`AlgebraicGeometry.Space.pushforwardModulesCompAt_assoc` at the morphisms of ringed topoi of
Stacks 03G8, and for the inverse images as its adjoint mate.

These were the hypotheses `AlgebraicGeometry.Space.ModulePushforwardCoherence.assoc` and
`AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`; both are now theorems.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`: **the associativity coherence of
  `AlgebraicGeometry.Space.modulePushforwardCompIso`**, which is the `assoc` field of
  `AlgebraicGeometry.Space.ModulePushforwardCoherence`.
* `AlgebraicGeometry.Space.modulePullbackCompIso_assoc` and
  `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`: **the associativity coherence of
  `AlgebraicGeometry.Space.modulePullbackCompIso`**, in the whiskered form and in the form of
  the predicate `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`, so that the reindexing
  calculus of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackAssoc.lean` becomes
  available with no hypothesis.
* `AlgebraicGeometry.Space.modulePullbackTriangle_assoc` and
  `AlgebraicGeometry.Space.modulePullbackTriangle_inv_app_assoc`: the same coherence for
  composites presented as single morphisms, which is the form a consumer indexed by a category
  of test objects needs, at the level of isomorphisms of functors and at a single module.
* `CategoryTheory.Functor.cocycle_iso_of_app` and
  `CategoryTheory.Functor.cocycle_app_of_iso`: the associativity cocycle law for a triple of
  composition comparisons, passing between its form at a single object and its form as an
  equality of isomorphisms of functors.
* `CategoryTheory.Functor.cocycle_app_of_iso_of_eq` and
  `CategoryTheory.Functor.comp_app_naturality_of_eq`: the same law, and the naturality of a
  single comparison, with the comparison morphisms supplied between the *uncomposed* objects
  `q.obj (p.obj N)` and identified with the components by hypotheses — the form an
  object-indexed cocycle condition is stated in.
* `CategoryTheory.Functor.map_comp_eq_comp_of_heq`: transport of such an identity along
  equalities of the four objects it is stated at, one object and one morphism at a time.

## Implementation notes

Everything here is stated and proved **at the level of isomorphisms of functors**, and the
passage to a single module is isolated in the two general lemmas
`CategoryTheory.Functor.cocycle_iso_of_app` and `CategoryTheory.Functor.cocycle_app_of_iso`.
This is what makes the proofs go through, and the reason is the one recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompTransport.lean`:
`AlgebraicGeometry.Space.modulePushforwardCompIso` differs from the comparison at the morphisms
of ringed topoi by transports along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, an equality of functors, and
`eqToHom` is `Eq.mpr`-based, so every spelling that puts those transports into a composition of
*morphisms* sends the elaborator into a reduction of
`AlgebraicGeometry.Space.modulePushforward` that does not terminate.  At the level of
isomorphisms nothing is projected and the transports are never reduced.

A second obstruction, also recorded there, is that the two comparisons are stated in two
spellings of one category of modules: `AlgebraicGeometry.Space.Modules` presents the structure
ring sheaf as `AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed *site*, while
`Stacks.Sheaves.RingedToposModules.pushforwardModules` presents it as
`Stacks.SheafOfModules.Tensor.ringSheaf` of the small étale ringed *topos*.  Reconciling the two
across a composition of morphisms is again a
nonterminating reduction, but reconciling them once at an equality of *functors* is cheap, and
that is what `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward'` and
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr'` do: they are the two inputs
restated in the `AlgebraicGeometry.Space.Modules` spelling, after which the transport law
applies with no reduction at all.  No raised heartbeat budget and no `set_option` is needed.

Associativity of composition in `AlgebraicGeometry.AlgebraicSpaces` holds by definitional
unfolding, so `(f ≫ g) ≫ h` and `f ≫ g ≫ h` are the same morphism; the two spellings of the
triple composite are nevertheless not syntactically equal, and
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr_assoc` fixes the right-hand
one once so that the two halves of the cocycle law share a single transport.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]

/-- The associativity cocycle law for three composition comparisons, read as an equality of
isomorphisms of functors: the two ways of comparing `p ⋙ q ⋙ r` with `pqr` agree. -/
theorem cocycle_iso_of_app {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {r : A₂ ⥤ A₃} {pq : A₀ ⥤ A₂}
    {qr : A₁ ⥤ A₃} {pqr : A₀ ⥤ A₃} (P : p ⋙ q ≅ pq) (Q : q ⋙ r ≅ qr) (PQ : pq ⋙ r ≅ pqr)
    (QR : p ⋙ qr ≅ pqr)
    (hcoc : ∀ N, r.map (P.hom.app N) ≫ PQ.hom.app N = Q.hom.app (p.obj N) ≫ QR.hom.app N) :
    isoWhiskerLeft p Q ≪≫ QR = (associator p q r).symm ≪≫ isoWhiskerRight P r ≪≫ PQ := by
  ext N
  simpa using (hcoc N).symm

/-- The associativity cocycle law for three composition comparisons, read at a single object.
This is the converse of `CategoryTheory.Functor.cocycle_iso_of_app`. -/
theorem cocycle_app_of_iso {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {r : A₂ ⥤ A₃} {pq : A₀ ⥤ A₂}
    {qr : A₁ ⥤ A₃} {pqr : A₀ ⥤ A₃} (P : p ⋙ q ≅ pq) (Q : q ⋙ r ≅ qr) (PQ : pq ⋙ r ≅ pqr)
    (QR : p ⋙ qr ≅ pqr)
    (h : isoWhiskerLeft p Q ≪≫ QR = (associator p q r).symm ≪≫ isoWhiskerRight P r ≪≫ PQ)
    (N : A₀) :
    r.map ((P.app N).hom) ≫ (PQ.app N).hom = Q.hom.app (p.obj N) ≫ (QR.app N).hom := by
  have key := NatTrans.congr_app (congrArg Iso.hom h) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp] at key
  simpa only [Iso.app_hom] using key.symm

/-- The associativity cocycle law at a single object, with the three comparison morphisms
supplied as morphisms **between the uncomposed objects** `q.obj (p.obj N)` rather than as
components of the comparisons of composite functors, and identified with those components by
three hypotheses.

This is the form in which a cocycle condition indexed by objects — rather than by functors — is
discharged.  Such a condition has to speak of `q.obj (p.obj N)`, because the object it transports
is given on its own and not as the value of a composite; the comparison isomorphisms that prove
it are components at `N` of isomorphisms of composite functors, whose source is `(p ⋙ q).obj N`.
The two agree definitionally, but reconciling them inside a composition of morphisms means
reducing `CategoryTheory.Iso.app` of a composite comparison far enough to project its `hom`, and
on the concrete comparisons of Stacks 03LU that reduction does not terminate.  Here the
reconciliation is confined to the three hypotheses, where it is a reduction of nothing: `p` and
`q` are variables. -/
theorem cocycle_app_of_iso_of_eq {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {r : A₂ ⥤ A₃} {pq : A₀ ⥤ A₂}
    {qr : A₁ ⥤ A₃} {pqr : A₀ ⥤ A₃} (P : p ⋙ q ≅ pq) (Q : q ⋙ r ≅ qr) (PQ : pq ⋙ r ≅ pqr)
    (QR : p ⋙ qr ≅ pqr)
    (h : isoWhiskerLeft p Q ≪≫ QR = (associator p q r).symm ≪≫ isoWhiskerRight P r ≪≫ PQ)
    (N : A₀) (tP : q.obj (p.obj N) ⟶ pq.obj N) (tPQ : r.obj (pq.obj N) ⟶ pqr.obj N)
    (tQ : r.obj (q.obj (p.obj N)) ⟶ qr.obj (p.obj N)) (tQR : qr.obj (p.obj N) ⟶ pqr.obj N)
    (hP : tP = (P.app N).hom) (hPQ : tPQ = (PQ.app N).hom) (hQ : tQ = Q.hom.app (p.obj N))
    (hQR : tQR = (QR.app N).hom) :
    r.map tP ≫ tPQ = tQ ≫ tQR := by
  subst hP
  subst hPQ
  subst hQ
  subst hQR
  exact cocycle_app_of_iso P Q PQ QR h N

/-- Transport of an identity `G.map tf ≫ tg = κ ≫ tgf` along equalities of the four objects it
is stated at, with the morphisms matched by `HEq`.

This is what carries an identity proved at one spelling of its objects to the *same* identity at
another spelling of them.  It is stated so that an application is pure first-order matching: the
unprimed objects and morphisms are determined by the identity one wants, the primed ones by the
identity one has, and each of the eight remaining obligations is a `rfl` or a `HEq.rfl` between
two fully determined terms.  Reconciling the two spellings inside a *single* unification problem
instead is what does not terminate on the concrete comparisons of Stacks 03LU; discharged one
object and one morphism at a time, as here, it is immediate. -/
theorem map_comp_eq_comp_of_heq {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (G : C ⥤ D) {a a' b b' : C} {c c' x x' : D} (ha : a = a') (hb : b = b') (hc : c = c')
    (hx : x = x') (tf : a ⟶ b) (tg : G.obj b ⟶ c) (κ : G.obj a ⟶ x) (tgf : x ⟶ c)
    (tf' : a' ⟶ b') (tg' : G.obj b' ⟶ c') (κ' : G.obj a' ⟶ x') (tgf' : x' ⟶ c')
    (htf : HEq tf tf') (htg : HEq tg tg') (hκ : HEq κ κ') (htgf : HEq tgf tgf')
    (h : G.map tf' ≫ tg' = κ' ≫ tgf') :
    G.map tf ≫ tg = κ ≫ tgf := by
  subst ha
  subst hb
  subst hc
  subst hx
  obtain rfl := eq_of_heq htf
  obtain rfl := eq_of_heq htg
  obtain rfl := eq_of_heq hκ
  obtain rfl := eq_of_heq htgf
  exact h

/-- Naturality of a composition comparison at two objects, with its two components supplied as
morphisms **between the uncomposed objects** and identified with the components by two
hypotheses, and with the functorial action on the source written as `q.map (p.map a)` rather than
as `(p ⋙ q).map a`.

This is the companion of `CategoryTheory.Functor.cocycle_app_of_iso_of_eq`, and it is needed for
the same reason: a morphism of object-indexed glueing data has to commute with transitions
written at `q.obj (p.obj N)`. -/
theorem comp_app_naturality_of_eq {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {pq : A₀ ⥤ A₂} (P : p ⋙ q ≅ pq)
    {N M : A₀} (a : N ⟶ M) (tN : q.obj (p.obj N) ⟶ pq.obj N) (tM : q.obj (p.obj M) ⟶ pq.obj M)
    (hN : tN = (P.app N).hom) (hM : tM = (P.app M).hom) :
    q.map (p.map a) ≫ tM = tN ≫ pq.map a := by
  subst hN
  subst hM
  simpa only [Iso.app_hom, Functor.comp_map] using P.hom.naturality a

/-- Transporting three composition comparisons along equalities of functors preserves the
associativity cocycle law, read as an equality of isomorphisms of functors. -/
theorem compIsoCongr_cocycle_iso {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {r r' : A₂ ⥤ A₃}
    {pq pq' : A₀ ⥤ A₂} {qr qr' : A₁ ⥤ A₃} {pqr pqr' : A₀ ⥤ A₃} (hp : p = p') (hq : q = q')
    (hr : r = r') (hpq : pq = pq') (hqr : qr = qr') (hpqr : pqr = pqr') (P : p ⋙ q ≅ pq)
    (Q : q ⋙ r ≅ qr) (PQ : pq ⋙ r ≅ pqr) (QR : p ⋙ qr ≅ pqr)
    (hcoc : isoWhiskerLeft p Q ≪≫ QR =
      (associator p q r).symm ≪≫ isoWhiskerRight P r ≪≫ PQ) :
    isoWhiskerLeft p' (compIsoCongr hq hr hqr Q) ≪≫ compIsoCongr hp hqr hpqr QR =
      (associator p' q' r').symm ≪≫ isoWhiskerRight (compIsoCongr hp hq hpq P) r' ≪≫
        compIsoCongr hpq hr hpqr PQ := by
  subst hp
  subst hq
  subst hr
  subst hpq
  subst hqr
  subst hpqr
  simpa [compIsoCongr] using hcoc

/-- **The associativity cocycle law survives a transport along equalities of functors**, stated
for comparisons that are merely *known to be* such transports.  This is the form in which the
coherence of a comparison defined elsewhere is obtained: the four equalities `hP`, `hQ`, `hPQ`,
`hQR` identify the comparisons with transported ones, and nothing about them is reduced. -/
theorem cocycle_iso_of_eq_compIsoCongr {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {r r' : A₂ ⥤ A₃}
    {pq pq' : A₀ ⥤ A₂} {qr qr' : A₁ ⥤ A₃} {pqr pqr' : A₀ ⥤ A₃} (hp : p = p') (hq : q = q')
    (hr : r = r') (hpq : pq = pq') (hqr : qr = qr') (hpqr : pqr = pqr') {P : p ⋙ q ≅ pq}
    {Q : q ⋙ r ≅ qr} {PQ : pq ⋙ r ≅ pqr} {QR : p ⋙ qr ≅ pqr} {P' : p' ⋙ q' ≅ pq'}
    {Q' : q' ⋙ r' ≅ qr'} {PQ' : pq' ⋙ r' ≅ pqr'} {QR' : p' ⋙ qr' ≅ pqr'}
    (hP : P' = compIsoCongr hp hq hpq P) (hQ : Q' = compIsoCongr hq hr hqr Q)
    (hPQ : PQ' = compIsoCongr hpq hr hpqr PQ) (hQR : QR' = compIsoCongr hp hqr hpqr QR)
    (hcoc : isoWhiskerLeft p Q ≪≫ QR =
      (associator p q r).symm ≪≫ isoWhiskerRight P r ≪≫ PQ) :
    isoWhiskerLeft p' Q' ≪≫ QR' =
      (associator p' q' r').symm ≪≫ isoWhiskerRight P' r' ≪≫ PQ' := by
  subst hP
  subst hQ
  subst hPQ
  subst hQR
  exact compIsoCongr_cocycle_iso hp hq hr hpq hqr hpqr P Q PQ QR hcoc

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X Y Z : AlgebraicSpaces B S hS}

/-! ### The two inputs, restated in the `AlgebraicGeometry.Space.Modules` spelling -/

/-- `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` read as an equality in the
category `AlgebraicGeometry.Space.Modules`, whose structure ring sheaf is that of the small
étale ringed *site*.  The two spellings of that category are definitionally equal, and
reconciling them once here is what keeps the comparisons below from being reduced. -/
theorem pushforwardModules_eq_modulePushforward' (f : X ⟶ Y) :
    @Eq (Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
      (smallEtaleRingedToposHom B S hS f).pushforwardModules (modulePushforward B S hS f) :=
  pushforwardModules_eq_modulePushforward B S hS f

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` with its three transports
read through `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward'`. -/
theorem modulePushforwardCompIso_eq_compIsoCongr' (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardCompIso B S hS f g =
      Functor.compIsoCongr (pushforwardModules_eq_modulePushforward' B S hS f)
        (pushforwardModules_eq_modulePushforward' B S hS g)
        (pushforwardModules_eq_modulePushforward' B S hS (f ≫ g))
        (pushforwardModulesCompAt B S hS f g) :=
  modulePushforwardCompIso_eq_compIsoCongr B S hS f g

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr'` for a composite whose
first factor is itself a composite, with the triple composite spelled `f ≫ g ≫ h`.  Fixing that
spelling is what lets the two halves of the cocycle law share one transport. -/
theorem modulePushforwardCompIso_eq_compIsoCongr_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    modulePushforwardCompIso B S hS (f ≫ g) h =
      Functor.compIsoCongr (pushforwardModules_eq_modulePushforward' B S hS (f ≫ g))
        (pushforwardModules_eq_modulePushforward' B S hS h)
        (pushforwardModules_eq_modulePushforward' B S hS (f ≫ g ≫ h))
        (pushforwardModulesCompAt B S hS (f ≫ g) h) :=
  modulePushforwardCompIso_eq_compIsoCongr' B S hS (f ≫ g) h

/-! ### The associativity coherence of the direct-image comparison -/

/-- **Stacks 03LU, associativity of the composition comparison for direct images.**  For three
composable morphisms `f : W ⟶ X`, `g : X ⟶ Y`, `h : Y ⟶ Z` of algebraic spaces the two ways of
comparing `f_* ∘ g_* ∘ h_*` with `(f ≫ g ≫ h)_*` agree.

This is the `assoc` field of `AlgebraicGeometry.Space.ModulePushforwardCoherence`, so it is no
longer a hypothesis.  It is the cocycle law at the morphisms of ringed topoi of Stacks 03G8,
`AlgebraicGeometry.Space.pushforwardModulesCompAt_assoc`, transported along the identifications
of the two direct images. -/
@[stacks 03LU "the associativity of the composition comparison for direct images"]
theorem modulePushforwardCompIso_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerLeft (modulePushforward B S hS f) (modulePushforwardCompIso B S hS g h) ≪≫
        modulePushforwardCompIso B S hS f (g ≫ h) =
      (associator (modulePushforward B S hS f) (modulePushforward B S hS g)
          (modulePushforward B S hS h)).symm ≪≫
        isoWhiskerRight (modulePushforwardCompIso B S hS f g)
          (modulePushforward B S hS h) ≪≫
        modulePushforwardCompIso B S hS (f ≫ g) h :=
  Functor.cocycle_iso_of_eq_compIsoCongr
    (pushforwardModules_eq_modulePushforward' B S hS f)
    (pushforwardModules_eq_modulePushforward' B S hS g)
    (pushforwardModules_eq_modulePushforward' B S hS h)
    (pushforwardModules_eq_modulePushforward' B S hS (f ≫ g))
    (pushforwardModules_eq_modulePushforward' B S hS (g ≫ h))
    (pushforwardModules_eq_modulePushforward' B S hS (f ≫ g ≫ h))
    (modulePushforwardCompIso_eq_compIsoCongr' B S hS f g)
    (modulePushforwardCompIso_eq_compIsoCongr' B S hS g h)
    (modulePushforwardCompIso_eq_compIsoCongr_assoc B S hS f g h)
    (modulePushforwardCompIso_eq_compIsoCongr' B S hS f (g ≫ h))
    (Functor.cocycle_iso_of_app (pushforwardModulesCompAt B S hS f g)
      (pushforwardModulesCompAt B S hS g h) (pushforwardModulesCompAt B S hS (f ≫ g) h)
      (pushforwardModulesCompAt B S hS f (g ≫ h))
      (pushforwardModulesCompAt_assoc B S hS f g h))

/-! ### The associativity coherence of the inverse-image comparison -/

/-- **Stacks 03LU, associativity of the composition comparison for inverse images.**  For three
composable morphisms `f : W ⟶ X`, `g : X ⟶ Y`, `h : Y ⟶ Z` of algebraic spaces the two ways of
comparing `h^* ∘ g^* ∘ f^*` with `(f ≫ g ≫ h)^*` agree.

It is the adjoint mate of `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`: the
comparison of inverse images is the comparison of left adjoints induced by the comparison of
direct images, and such an induced comparison inherits the coherence. -/
theorem modulePullbackCompIso_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerLeft (modulePullback B S hS h) (modulePullbackCompIso B S hS f g) ≪≫
        modulePullbackCompIso B S hS (f ≫ g) h =
      (associator (modulePullback B S hS h) (modulePullback B S hS g)
          (modulePullback B S hS f)).symm ≪≫
        isoWhiskerRight (modulePullbackCompIso B S hS g h) (modulePullback B S hS f) ≪≫
        modulePullbackCompIso B S hS f (g ≫ h) := by
  simp only [modulePullbackCompIso_eq_leftAdjointCompIso]
  exact
    Adjunction.leftAdjointCompIso_assoc (modulePullbackAdjunction B S hS h)
      (modulePullbackAdjunction B S hS g) (modulePullbackAdjunction B S hS f)
      (modulePullbackAdjunction B S hS (g ≫ h)) (modulePullbackAdjunction B S hS (f ≫ g))
      (modulePullbackAdjunction B S hS (f ≫ g ≫ h))
      (modulePushforwardCompIso B S hS g h) (modulePushforwardCompIso B S hS f g)
      (modulePushforwardCompIso B S hS (f ≫ g) h)
      (modulePushforwardCompIso B S hS f (g ≫ h)) (modulePushforwardCompIso_assoc B S hS f g h)

/-- The associativity coherence of the comparison of inverse images, in the form of the
predicate `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`.  The reindexing calculus of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackAssoc.lean` is therefore available
with no hypothesis. -/
theorem modulePullbackCompIsoAssoc : ModulePullbackCompIsoAssoc B S hS where
  hom_app f g h M := Functor.cocycle_app_of_iso _ _ _ _ (modulePullbackCompIso_assoc B S hS f g h) M

/-! ### The coherence for composites presented as single morphisms -/

/-- **The comparison of inverse images along composites is compatible with composition.**  For
`f : W ⟶ X`, `g : X ⟶ Y` and `p : Y ⟶ Z`, breaking the inverse image along the triple composite
into three steps through `f ≫ g` or through `g ≫ p` gives the same comparison.

This is `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_comp` with
its hypothesis discharged. -/
theorem modulePullbackTriangle_assoc
    {f : W ⟶ X} {g : X ⟶ Y} {p : Y ⟶ Z} {k : W ⟶ Y} {q : X ⟶ Z} {r : W ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r) :
    modulePullbackTriangle B S hS hkr ≪≫
        isoWhiskerLeft (modulePullback B S hS p) (modulePullbackTriangle B S hS hk) =
      modulePullbackTriangle B S hS hr ≪≫
        isoWhiskerRight (modulePullbackTriangle B S hS hq) (modulePullback B S hS f) ≪≫
        associator (modulePullback B S hS p) (modulePullback B S hS g)
          (modulePullback B S hS f) := by
  subst hk
  subst hq
  have hE : modulePullbackTriangle B S hS hr =
      eqToIso (congrArg (modulePullback B S hS) hkr.symm) ≪≫
        (modulePullbackCompIso B S hS f (g ≫ p)).symm := rfl
  rw [modulePullbackTriangle_eq hkr, hE, modulePullbackTriangle_rfl,
    modulePullbackTriangle_rfl, Iso.trans_assoc, Iso.trans_assoc]
  refine congrArg (fun t ↦ eqToIso (congrArg (modulePullback B S hS) hkr.symm) ≪≫ t) ?_
  have key := modulePullbackCompIso_assoc B S hS f g p
  rw [← Iso.symm_eq_iff] at key
  simpa [Functor.isoWhiskerLeft_symm, Functor.isoWhiskerRight_symm] using key

/-- `AlgebraicGeometry.Space.modulePullbackTriangle_assoc` at a single module, on the
splitting comparisons. -/
theorem modulePullbackTriangle_inv_app_assoc
    {f : W ⟶ X} {g : X ⟶ Y} {p : Y ⟶ Z} {k : W ⟶ Y} {q : X ⟶ Z} {r : W ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullback B S hS f).map ((modulePullbackTriangle B S hS hq).inv.app M) ≫
        (modulePullbackTriangle B S hS hr).inv.app M =
      (modulePullbackTriangle B S hS hk).inv.app ((modulePullback B S hS p).obj M) ≫
        (modulePullbackTriangle B S hS hkr).inv.app M := by
  have key := NatTrans.congr_app
    (congrArg Iso.inv (modulePullbackTriangle_assoc B S hS hk hq hr hkr)) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] at key
  exact key.symm

end AlgebraicGeometry.Space

end
