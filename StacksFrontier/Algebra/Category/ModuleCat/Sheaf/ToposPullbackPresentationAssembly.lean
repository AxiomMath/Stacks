module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationEncode
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationTransport
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback along a morphism of ringed topoi preserves finite presentation

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `F` be a
sheaf of `O_D`-modules of finite presentation.  Stacks 03DO, for the clause 03DL (7), asserts
that the pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6 (2) is again of finite
presentation.  This file assembles that statement from the five pieces that precede it.

## The route, and why it is not the Stacks one

Stacks proves 03DO by reducing to Section 03DG, which works on sites *having all finite
limits*, and so would require the site hypotheses `HasFiniteLimits C` / `HasBinaryProducts C`.
Stacks assumes no such thing of a ringed site, so acquiring them would narrow the theorem.
The route taken here instead localizes neither the sites nor the morphism, and reads the
condition 03DL (7) on *sections* throughout:

1. `Stacks.Sheaves.LocalGeneration.presDataSheaf F n m` is the sheaf of sets on the target
   site whose sections over an object `W` are the presentations of `F` over `W` by `n`
   generating sections and `m` relation tuples.  It is a subsheaf of `F^n × (O_D^n)^m`.
2. `Stacks.Sheaves.LocalGeneration.jointlyLocallyInhabited_presDataSheaf`: if `F` is of finite
   presentation then the family `(n, m) ↦ presDataSheaf F n m`, indexed by `ℕ × ℕ`, is jointly
   locally inhabited — every object of the target site is covered by objects over which some
   member has a section.
3. `Stacks.Topos.exists_cover_inverseImage_sections`: joint local inhabitedness transports
   along `f⁻¹`, so every object of the *source* site is covered by objects carrying a section
   of `f⁻¹(presDataSheaf F n m)` for some `(n, m)`.
4. `Stacks.Sheaves.PresentationTransport.isPresentationData_pullback`: such a section is
   presentation data for `f⁻¹F`, with the same `n` and the same `m`.
5. `Stacks.SheafOfModules.exists_isFinite_presentation_over_of_isPresentationData`: that data
   decodes into a finite `((f⁻¹F).over V).Presentation`, which is Mathlib's spelling.

Step 5 feeds the `hF` hypothesis of
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules_of_inverseImage_local`,
which supplies the extension-of-scalars half along `f⁻¹O_D ⟶ O_C` and assembles the local
presentations into a `SheafOfModules.QuasicoherentData`.

## Main results

* `Stacks.Sheaves.PresentationTransport.exists_cover_isFinite_presentation_inverseImage`:
  steps 2–5, for an arbitrary `Stacks.Sheaves.ToposPullback.PullbackModuleData` — every object
  of the source site has a covering on whose members the inverse image of a finitely presented
  sheaf of modules has a finite presentation.
* `Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules`: **Stacks 03DO for
  the clause 03DL (7)**, the pullback of a finitely presented sheaf of modules along a
  morphism of ringed topoi is of finite presentation.

## The sibling clause 03DL (2), which this route also reaches

Stacks 03DO for the clause 03DL (2) — the pullback of a *finite locally free* sheaf of modules is
finite locally free — is proved for an arbitrary morphism of ringed topoi in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFiniteLocallyFree`, as
`Stacks.Sheaves.FinitePresentation.isFiniteLocallyFreeOnSite_pullbackModules`, **by this file's
route with the relation count fixed at `0`**.

Freeness looks as though it could not travel along `f⁻¹`: "the map `O^n ⟶ F` is an isomorphism"
is not a geometric statement, and the usual fix — carrying the inverse as a section of an
internal Hom — would need a comparison `f⁻¹𝓗om(F, G) ⟶ 𝓗om(f⁻¹F, f⁻¹G)` compatible with
evaluation, which this development does not have.  **No such comparison is needed: finite
freeness is finite presentation with zero relations, and this file's machinery is already
parameterized by the number of relations.**  Concretely, at `m = 0`:

* `Stacks.Sheaves.LocalGeneration.relationSpanSieve R (t : Fin 0 → _) a` is the sieve of arrows
  along which every `a i` restricts to `0`, since the empty sum is `0`; so condition (C) of
  `Stacks.Sheaves.LocalGeneration.IsPresentationData`,
  `Stacks.Sheaves.LocalGeneration.LocallySpansKernel M s t`, says at `m = 0` that every relation
  among the `s` vanishes locally, hence vanishes, `O.obj` being a sheaf;
* with condition (B), `LocallySpans M s`, that makes `O^n ⟶ M` both a monomorphism and an
  epimorphism, so an isomorphism, the slice category of sheaves of modules being abelian and
  hence balanced.

So `presDataSheaf M n 0` is the sheaf of rank-`n` trivializations of `M`, and steps 3 and 4 of the
route above — `Stacks.Topos.exists_cover_inverseImage_sections` and
`Stacks.Sheaves.PresentationTransport.isPresentationData_pullback`, which carries the data with
*the same* `n` and *the same* `m` — apply to it unchanged, over the index `ℕ` rather than
`ℕ × ℕ`.  What had to be written was the encoding and the decoding at `m = 0`, and they are
`Stacks.Sheaves.LocalGeneration.exists_isPresentationData_of_isFiniteFree` and
`Stacks.Sheaves.LocalGeneration.isFiniteFree_of_isPresentationData_zero` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsZeroRelations`, together with the
analogue of `Stacks.Sheaves.LocalGeneration.jointlyLocallyInhabited_presDataSheaf` for the family
`fun n : ℕ => presDataSheaf M n 0`.  Note that
`Stacks.SheafOfModules.exists_isFinite_presentation_over_of_isPresentationData` cannot be reused
for the decoding: its existential loses the relation count, so the presenting morphism cannot be
seen as invertible through it.

The extension-of-scalars half is
`Stacks.Sheaves.FinitePresentation.isFiniteFree_extendScalarsOver`, one instantiation of
`Stacks.Sheaves.LocalizedPullback.isFiniteFree_map` at the left adjoint `extendScalarsOver`.

## Implementation notes

**No coproduct over `ℕ × ℕ`.**  Neither `HasSheafify J (Type w)` nor
`HasCoproduct (A : ℕ × ℕ → Sheaf J (Type w))` is available at these universes — `w` is the
section universe of the topos and is unrelated to the site's `max u v` at which Mathlib
sheafifies type-valued presheaves.  `ℕ × ℕ` therefore appears only as the index of a family
for `Stacks.Topos.JointlyLocallyInhabited`, which is defined by a sieve and forms no colimit.
This is the reason the argument is phrased through joint local inhabitedness rather than
through local surjectivity of `∐ (n, m), presDataSheaf F n m ⟶ ⊤`.

**`HasSheafify` on the slice sites is derived, not assumed.**
`Stacks.SheafOfModules.exists_isFinite_presentation_over_of_isPresentationData` asks for
`∀ Z, HasSheafify (J.over Z) AddCommGrpCat.{w}`, which
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective` produces from the
`HasWeakSheafify` and `WEqualsLocallyBijective` hypotheses already present.  That is a
*theorem* and not an instance, so it is invisible to instance search and is supplied by a
`let`; the class is a proposition, so this is the same instance as any other.

**Universes.**  The generic statement keeps all six universes of
`Stacks.Sheaves.ToposPullback.PullbackModuleData` independent: the two sites `C : Type u`,
`D : Type u'` with `Category.{v}`, `Category.{v'}`, and the two section universes `w`, `w'` of
the two topoi.  The ringed-topoi statement has the two structure sheaves in one universe `w`,
which is forced by `Stacks.Sheaves.RingedToposModules.pullbackModules`: extension of scalars
along `f⁻¹O_D ⟶ O_C` is a morphism of sheaves of rings on the source site, so the two
structure sheaves must take sections in the same universe.  Nothing else is narrowed, and no
hypothesis on the sites beyond the ones the inputs carry is added — in particular no finite
limits, no products and no smallness.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.PresentationTransport

open Stacks.Sheaves.LocalGeneration Stacks.Topos

universe v u v' u' w w'

section Assembly

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [∀ Z : C, HasWeakSheafify (J.over Z) AddCommGrpCat.{w}]
  [∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ Z : D, HasWeakSheafify (K.over Z) AddCommGrpCat.{w'}]
  [∀ Z : D, (K.over Z).WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **The inverse-image half of Stacks 03DO for the clause 03DL (7).**  If `F` is a sheaf of
`O`-modules of finite presentation on the target site, then every object `U` of the source site
has a covering on whose members the inverse image `f⁻¹F` of Stacks 03D2 has a finite
presentation.

The covering is the one `Stacks.Topos.exists_cover_inverseImage_sections` produces for the
family of presentation-data sheaves of `F`, so no colimit over the index `ℕ × ℕ` of that family
is formed; see the module documentation. -/
theorem exists_cover_isFinite_presentation_inverseImage
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (R : Sheaf K RingCat.{w'}) (P : ToposPullback.PullbackModuleData J K f R)
    (M : SheafOfModules.{w'} R) [M.IsFinitePresentation] (U : C) :
    ∃ T : J.Cover U, ∀ (V : C) (g : V ⟶ U), T g →
      ∃ Q : ((P.moduleFunctor.obj M).over V).Presentation, Q.IsFinite := by
  obtain ⟨T, hT⟩ := exists_cover_inverseImage_sections f
    (fun q : ℕ × ℕ => presDataSheaf M q.1 q.2) (jointlyLocallyInhabited_presDataSheaf M) U
  refine ⟨T, fun V g hg => ?_⟩
  obtain ⟨q, ⟨p⟩⟩ := hT V g hg
  let _ : ∀ Z : C, HasSheafify (J.over Z) AddCommGrpCat.{w} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact Stacks.SheafOfModules.exists_isFinite_presentation_over_of_isPresentationData
    (P.moduleFunctor.obj M) _ _
    (isPresentationData_pullback f R P M (presentationDataSheaf R M q.1 q.2) p)

end Assembly

end Stacks.Sheaves.PresentationTransport

namespace Stacks.Sheaves.FinitePresentation

open AlgebraicGeometry Stacks.Sheaves.PresentationTransport
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback

universe v u v' u' w

/-- **Stacks 03DO for the clause 03DL (7): pullback preserves finite presentation.**  The
pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6 (2) of a sheaf of `O_D`-modules of finite
presentation along a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is of
finite presentation.

The two halves are
`Stacks.Sheaves.PresentationTransport.exists_cover_isFinite_presentation_inverseImage`, which
produces a covering of each object of the source site carrying a finite presentation of
`f⁻¹F`, and
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules_of_inverseImage_local`,
which transports those presentations across extension of scalars along `f⁻¹O_D ⟶ O_C` and
assembles them. -/
@[stacks 03DO "part (7), finite presentation: for an arbitrary morphism of ringed topoi",
  ega "0 5.2.5" "more general"]
instance isFinitePresentation_pullbackModules {X : RingedTopos.{v, u, w}}
    {Y : RingedTopos.{v', u', w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [F.IsFinitePresentation] : ((f.pullbackModules).obj F).IsFinitePresentation :=
  isFinitePresentation_pullbackModules_of_inverseImage_local f F fun U =>
    exists_cover_isFinite_presentation_inverseImage f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (pullbackModule X.J Y.J f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) F U

end Stacks.Sheaves.FinitePresentation

end
