module

public import StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian

/-!
# A system of abelian sheaves over a fixed diagram of spectral spaces

`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem`
(the Tag 0A37 development) encodes "a cofiltered system of spectral spaces with an
abelian sheaf on each member and compatible `f_a`-maps" as a **single functor**
`E : K ⥤ SheafedSpace AddCommGrpCat`, exactly as the `Type`-valued
`SpectralSheafSystem` (`StacksFrontier/Topology/Sheaves/Limits/DescendOpens.lean`) encodes it as a
functor into `PresheafedSpace`.  That bundling is convenient as long as there is only one sheaf
system in play.

The proof of Stacks 0A37 varies the **sheaf** system while keeping the **space** diagram fixed:
for an injective embedding `ℱᵢ ↪ 𝒢ᵢ` one needs a second system over the same spaces.  With the
bundled encoding a second system means a second functor `E' : K ⥤ SheafedSpace` together with the
assertion `E' ⋙ forget = E ⋙ forget`, and its `map_id`/`map_comp` obligations have to be
discharged against the `eqToHom` that mediates between `(f_{b ≫ a})_*` and `(f_a)_*(f_b)_*`.

This file splits the two halves.  `SpectralDiagram.AbelianSystem D` is the data of an abelian
sheaf on each space of a **fixed** `SpectralDiagram D` together with compatible `f_a`-maps, with
the diagram a *parameter* rather than part of the data.  A second system over the same spaces is
then another term of the same type, and the coherence is stated once, inside the structure, in
terms of the restriction maps of the sheaves rather than of a transport of presheaves.

## Main definitions

* `SpectralDiagram.pre a V`: the preimage `f_a⁻¹V`, with `SpectralDiagram.pre_id` and
  `SpectralDiagram.pre_comp` the two identifications it satisfies, and
  `SpectralDiagram.preIdHom`, `SpectralDiagram.preCompHom` those identifications as arrows of
  `(Opens _)ᵒᵖ`.
* `SpectralDiagram.AbelianSystem`: the structure.  The `f_a`-map is a morphism of presheaves
  `push a : 𝒜ᵢ ⟶ (f_a)_*𝒜ⱼ`, so naturality in the open is part of the datum; the identity and
  cocycle laws are the fields `push_id` and `push_comp`.
* `SpectralDiagram.AbelianSystem.push_natTrans_id` and
  `SpectralDiagram.AbelianSystem.push_natTrans_comp`: the two laws as equations of arrows of
  presheaves, and `SpectralDiagram.abelianSystemOfNatTrans`, the constructor taking them in that
  form — which is the form a system defined by a universal property can verify.
* `SpectralDiagram.AbelianSystem.E`: the comparison functor `J ⥤ SheafedSpace AddCommGrpCat`,
  with `E_forget : A.E ⋙ SheafedSpace.forget _ = D.F` holding by `rfl`.
* `SpectralDiagram.AbelianSystem.toSpectralAbelianSheafSystem`: the system as a
  `SpectralAbelianSheafSystem`, which is what makes the abelian Stacks 0A33 and the
  Stacks 0A37 infrastructure apply to it unchanged.
* `Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.toAbelianSystem`: the converse,
  reading a bundled system as a system over its own underlying diagram.

## Main results

* `SpectralDiagram.AbelianSystem.toSpectralAbelianSheafSystem_baseDiagram`: the underlying space
  diagram of the comparison is `D.F` itself, by `rfl`.  This is the point of the whole file: a
  second `AbelianSystem` over the same `D` has *the same* base diagram on the nose, not merely up
  to isomorphism, so the cohomology comparison data of Stacks 0A37 — which is indexed by the
  spaces, the opens and the cone — is shared between the two systems with no transport.
* `Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.toAbelianSystem`: the converse
  comparison, so neither encoding loses information.

## Implementation notes

### Why the coherence is stated with a quantified arrow of opens

`f_{b ≫ a}⁻¹V` and `f_b⁻¹f_a⁻¹V` are *equal* opens — `SpectralDiagram.pre_comp` — but not
syntactically equal, because `D.F.map (b ≫ a) = D.F.map b ≫ D.F.map a` is `D.F.map_comp`, a
proof.  So the two sides of the cocycle law live in propositionally equal but distinct-looking
groups `𝒜ₖ(f_{b ≫ a}⁻¹V)` and `𝒜ₖ(f_b⁻¹f_a⁻¹V)`, and some arrow has to mediate.

Three spellings of that arrow were available.  A transport `eqToHom` of the *presheaves* is what
the bundled encoding uses and what has to be fought; a restriction along
`homOfLE (D.pre_comp b a V).le` is an honest arrow of the sheaf but puts `D.pre` inside the
statement, and a `rw` whose motive crosses that `def` is refused, which is how the first draft of
`E.map_comp` failed.  The spelling used here quantifies over an arbitrary arrow
`e : op (D.pre (b ≫ a) V) ⟶ op (D.pre b (D.pre a V))` of `(Opens Xₖ)ᵒᵖ`.  That loses nothing:
`Opens Xₖ` is a poset, so such an arrow is unique when it exists and exists exactly because
`pre_comp` holds (`SpectralDiagram.preCompHom` is the witness).  It gains that the obligation is
*already* in the shape `AlgebraicGeometry.SheafedSpace.ext` produces, so `E.map_id` and
`E.map_comp` are closed by `exact` with no rewriting at all.

`TopCat.Presheaf.map_comp_map_eq_id` is the one lemma behind both: two restrictions between
propositionally equal opens compose to the identity, because the composite arrow and the identity
are equal in a poset.

### Which way the comparison with `SpectralAbelianSheafSystem` goes

The two encodings are equivalent (`toAbelianSystem_toSpectralAbelianSheafSystem` and its
converse), so the choice is between re-expressing the abelian Stacks 0A33 machinery of
`StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian` over the new structure and building the
comparison.  **The comparison is much cheaper and is what is done here.**  Re-expressing would
mean restating `typeSystem`, `pullbackSystem`, `abelianPullbackSystem`,
`colimitSheafSectionsIso` and `isColimitAbelianStageCocone` — upwards of two thousand lines
across `DescendOpens.lean` and `DescendOpensAbelian.lean` — whereas `E` is twelve lines and
`E_forget` is `rfl`, which is the only thing the downstream statements need: every one of them is
phrased in terms of `S.E`, `S.baseDiagram` or `S.typeSystem.diagram`, and all three are literally
the corresponding data of `D` for `A.toSpectralAbelianSheafSystem`.

So the new structure is a *constructor* for `SpectralAbelianSheafSystem` with the base diagram
held fixed, and nothing downstream has to change.

### Universes

The structure is stated at `SpectralDiagram.{v, u}`, i.e. `J : Type v` small and spaces in
`TopCat.{max v u}`, mirroring `SpectralSheafSystem`.  The comparison therefore lands in
`SpectralAbelianSheafSystem.{max v u, v, v}`; at `v = u`, which is the universe assignment the
two colimit-comparison clauses of Stacks 0A37 are restated at, that is
`SpectralAbelianSheafSystem.{u, u, u}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open AlgebraicGeometry

universe v u

noncomputable section

/-- **Two restrictions between propositionally equal opens compose to the identity.**  `Opens X`
is a poset, so the composite `f ≫ g : op V ⟶ op V` is the identity, there being at most one
arrow between any two opens. -/
theorem TopCat.Presheaf.map_comp_map_eq_id {C : Type*} [Category C] {X : TopCat.{u}}
    (P : X.Presheaf C) {V W : Opens X} (f : op V ⟶ op W) (g : op W ⟶ op V) :
    P.map f ≫ P.map g = 𝟙 (P.obj (op V)) := by
  rw [← P.map_comp, Subsingleton.elim (f ≫ g) (𝟙 (op V)), P.map_id]

namespace SpectralDiagram

variable {J : Type v} [SmallCategory J] [IsCofiltered J] (D : SpectralDiagram.{v, u} J)

/-! ### The preimage of an open along a transition map -/

/-- The preimage `f_a⁻¹V ⊆ X_j` of an open `V ⊆ X_i` along the transition map of `a : j ⟶ i`. -/
def pre {j i : J} (a : j ⟶ i) (V : Opens (D.F.obj i)) : Opens (D.F.obj j) :=
  (Opens.map (D.F.map a)).obj V

/-- The preimage along an identity morphism is the open itself: `D.F.map (𝟙 j)` is the
identity. -/
lemma pre_id (j : J) (V : Opens (D.F.obj j)) : D.pre (𝟙 j) V = V := by
  rw [pre, D.F.map_id]; rfl

/-- Preimages compose: `f_{b ≫ a}⁻¹V = f_b⁻¹f_a⁻¹V`, by functoriality of `D.F`. -/
lemma pre_comp {k j i : J} (b : k ⟶ j) (a : j ⟶ i) (V : Opens (D.F.obj i)) :
    D.pre (b ≫ a) V = D.pre b (D.pre a V) := by
  rw [pre, pre, pre, D.F.map_comp]; rfl

/-- The identification `f_{𝟙}⁻¹V = V` of `pre_id`, as an arrow of `(Opens X_j)ᵒᵖ`.  It is the
unique such arrow. -/
def preIdHom (j : J) (V : Opens (D.F.obj j)) : op (D.pre (𝟙 j) V) ⟶ op V :=
  (homOfLE (D.pre_id j V).ge).op

/-- The identification `f_{b ≫ a}⁻¹V = f_b⁻¹f_a⁻¹V` of `pre_comp`, as an arrow of
`(Opens X_k)ᵒᵖ`.  It is the unique such arrow. -/
def preCompHom {k j i : J} (b : k ⟶ j) (a : j ⟶ i) (V : Opens (D.F.obj i)) :
    op (D.pre (b ≫ a) V) ⟶ op (D.pre b (D.pre a V)) :=
  (homOfLE (D.pre_comp b a V).ge).op

/-- `pre_id` as an arrow of *functors*, `f_{𝟙}⁻¹ = id` on opens.  This is the shape in which
`AlgebraicGeometry.SheafedSpace.ext` wants the identification, and the unique arrow of its
type: an arrow of functors into a poset is determined by nothing. -/
def preIdNatTrans (j : J) :
    (Opens.map (D.F.map (𝟙 j))).op ⟶ 𝟭 (Opens (D.F.obj j))ᵒᵖ :=
  eqToHom (by rw [D.F.map_id]; rfl)

/-- `pre_comp` as an arrow of *functors*, `f_{b ≫ a}⁻¹ = f_b⁻¹ ∘ f_a⁻¹` on opens. -/
def preCompNatTrans {k j i : J} (b : k ⟶ j) (a : j ⟶ i) :
    (Opens.map (D.F.map (b ≫ a))).op ⟶
      (Opens.map (D.F.map a)).op ⋙ (Opens.map (D.F.map b)).op :=
  eqToHom (by rw [D.F.map_comp]; rfl)

/-! ### The structure -/

/-- **A system of abelian sheaves over the fixed diagram of spectral spaces `D`.**

The data of Stacks 0A37 with the spaces held fixed: an abelian sheaf `𝒜ⱼ` on each `Xⱼ`, and for
each `a : j ⟶ i` an `f_a`-map `φ_a : 𝒜ᵢ ⟶ (f_a)_*𝒜ⱼ`, subject to the identity and cocycle laws.
Because `φ_a` is a morphism of presheaves, naturality of the `f_a`-map in the open is part of the
datum rather than a further field.

The two laws are stated through an arbitrary arrow of opens identifying the two spellings of the
target open; see the implementation notes of this file for why.  `𝒜ᵢ` is a sheaf, not merely a
presheaf; the spectrality of the spaces and of the transition maps is carried by `D`. -/
structure AbelianSystem where
  /-- The abelian sheaf on the `j`-th space of the diagram. -/
  sheaf : ∀ j : J, (D.F.obj j).Sheaf AddCommGrpCat.{max v u}
  /-- The `f_a`-map `φ_a : 𝒜ᵢ ⟶ (f_a)_*𝒜ⱼ`, as a morphism of presheaves of abelian groups. -/
  push : ∀ {j i : J} (a : j ⟶ i), (sheaf i).presheaf ⟶ (D.F.map a) _* (sheaf j).presheaf
  /-- The `f`-map of an identity morphism is the identity, read through the identification
  `f_{𝟙}⁻¹V = V`. -/
  push_id : ∀ (j : J) (V : Opens (D.F.obj j)) (e : op (D.pre (𝟙 j) V) ⟶ op V),
    (push (𝟙 j)).app (op V) ≫ (sheaf j).presheaf.map e = 𝟙 ((sheaf j).presheaf.obj (op V))
  /-- The cocycle law `φ_{b ≫ a} = φ_b ∘ φ_a`, read through the identification
  `f_{b ≫ a}⁻¹V = f_b⁻¹f_a⁻¹V`. -/
  push_comp : ∀ {k j i : J} (b : k ⟶ j) (a : j ⟶ i) (V : Opens (D.F.obj i))
      (e : op (D.pre (b ≫ a) V) ⟶ op (D.pre b (D.pre a V))),
    (push (b ≫ a)).app (op V) ≫ (sheaf k).presheaf.map e =
      (push a).app (op V) ≫ (push b).app (op (D.pre a V))

namespace AbelianSystem

variable {D} (A : D.AbelianSystem)

/-! ### The two laws in natural-transformation form

The fields are stated at a single open, which is what a construction defining its `f_a`-maps on
sections has to verify.  A construction defining them by a *universal property* — the injective
system `𝒢ᵢ = ∏_{b : k → i} f_{b,*}ℐₖ` of Stacks 0A37 is one, its `f_a`-maps coming from
`CategoryTheory.Limits.Pi.lift` — cannot read off a section at all without first passing through
the comparison of a product of sheaves with the pointwise product of their sections.  For such a
construction the laws are needed between morphisms of presheaves, and that is this section:
`push_natTrans_id` and `push_natTrans_comp` are the two fields read as arrow equations, and
`SpectralDiagram.abelianSystemOfNatTrans` is the constructor that takes them in that form.

The two directions are interderivable because the arrow of opens that the field quantifies over
is the component of the arrow of functors that the arrow equation quantifies over, and arrows of
`(Opens X)ᵒᵖ` between given objects are unique. -/

/-- The identity law as an equation of arrows of presheaves. -/
lemma push_natTrans_id (j : J) (e : (Opens.map (D.F.map (𝟙 j))).op ⟶ 𝟭 (Opens (D.F.obj j))ᵒᵖ) :
    A.push (𝟙 j) ≫ Functor.whiskerRight e (A.sheaf j).presheaf = 𝟙 (A.sheaf j).presheaf := by
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨V⟩ := V
  rw [NatTrans.comp_app, Functor.whiskerRight_app]
  exact A.push_id j V _

/-- The cocycle law as an equation of arrows of presheaves.  The right-hand side is the
`c`-component of a composite of morphisms of presheafed spaces, which is why this is the form
that `E.map_comp` consumes. -/
lemma push_natTrans_comp {k j i : J} (b : k ⟶ j) (a : j ⟶ i)
    (e : (Opens.map (D.F.map (b ≫ a))).op ⟶
      (Opens.map (D.F.map a)).op ⋙ (Opens.map (D.F.map b)).op) :
    A.push (b ≫ a) ≫ Functor.whiskerRight e (A.sheaf k).presheaf =
      A.push a ≫ (Presheaf.pushforward AddCommGrpCat.{max v u} (D.F.map a)).map (A.push b) := by
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨V⟩ := V
  rw [NatTrans.comp_app, Functor.whiskerRight_app]
  exact A.push_comp b a V _

/-! ### The comparison functor to sheafed spaces -/

/-- The `j`-th member of the system as a sheafed space.  An `abbrev` whose carrier field is
written out, so that instance search sees the carrier to be `D.F.obj j`. -/
abbrev space (j : J) : SheafedSpace.{_, _, max v u} AddCommGrpCat.{max v u} where
  carrier := D.F.obj j
  presheaf := (A.sheaf j).presheaf
  IsSheaf := (A.sheaf j).2

/-- The transition map of the system as a morphism of sheafed spaces: the transition map of `D`
on spaces, and the `f_a`-map on sheaves. -/
abbrev mor {j i : J} (a : j ⟶ i) : A.space j ⟶ A.space i :=
  InducedCategory.homMk { base := D.F.map a, c := A.push a }

/-- **The system as a functor into sheafed spaces.**  Its two functoriality obligations are
exactly `push_id` and `push_comp`: `AlgebraicGeometry.SheafedSpace.ext` reduces each of them to
the corresponding law at the arrow of opens that it produces itself. -/
def E : J ⥤ SheafedSpace.{_, _, max v u} AddCommGrpCat.{max v u} where
  obj := A.space
  map := A.mor
  map_id j := by
    refine SheafedSpace.ext _ _ (D.F.map_id j) (NatTrans.ext (funext fun V => ?_))
    obtain ⟨V⟩ := V
    rw [NatTrans.comp_app, Functor.whiskerRight_app]
    exact A.push_id j V _
  map_comp {k j i} b a := by
    refine SheafedSpace.ext _ _ (D.F.map_comp b a) (NatTrans.ext (funext fun V => ?_))
    obtain ⟨V⟩ := V
    rw [NatTrans.comp_app, Functor.whiskerRight_app]
    exact A.push_comp b a V _

/-- The functor `A.E` sends `j` to the sheafed space `A.space j`. -/
@[simp] lemma E_obj (j : J) : A.E.obj j = A.space j := rfl

/-- The functor `A.E` sends an arrow `a` to the transition morphism `A.mor a`. -/
@[simp] lemma E_map {j i : J} (a : j ⟶ i) : A.E.map a = A.mor a := rfl

/-- **The diagram of spaces underlying the comparison functor is `D.F` itself.**  The carrier of
`A.space j` is `D.F.obj j` and the base of `A.mor a` is `D.F.map a`, both by definition, so the
two functors agree on objects and on arrows. -/
lemma E_forget : A.E ⋙ SheafedSpace.forget _ = D.F := rfl

/-! ### The comparison with `SpectralAbelianSheafSystem` -/

/-- **The system as a `SpectralAbelianSheafSystem`.**  The bundled functor is `A.E`, and the two
spectrality fields are those of `D`.  This is what makes the abelian Stacks 0A33 and the
whole of the Stacks 0A37 infrastructure apply to an `AbelianSystem` with no restatement. -/
def toSpectralAbelianSheafSystem :
    Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.{max v u, v, v} J where
  E := A.E
  spectralSpace := D.isSpectralSpace
  spectralMap a := D.isSpectralMap a

/-- **The base diagram of the comparison is `D.F`.**  So two `AbelianSystem`s over one `D` give
two `SpectralAbelianSheafSystem`s with literally the same underlying diagram of spaces, which is
what the proof of Stacks 0A37 needs when it replaces `ℱ` by an injective `𝒢` over the same
spaces. -/
lemma toSpectralAbelianSheafSystem_baseDiagram :
    A.toSpectralAbelianSheafSystem.baseDiagram = D.F := rfl

end AbelianSystem

/-- **A system of abelian sheaves from the two laws in natural-transformation form.**  Every
field but the two laws is passed through; each law is the given arrow equation read at the open,
the arrow of opens that the field quantifies over being the component of the arrow of functors
`preIdNatTrans` / `preCompNatTrans` by uniqueness of arrows in `(Opens _)ᵒᵖ`.

This is the constructor for a system whose `f_a`-maps come from a universal property rather than
from a formula on sections. -/
def abelianSystemOfNatTrans
    (sheaf : ∀ j : J, (D.F.obj j).Sheaf AddCommGrpCat.{max v u})
    (push : ∀ {j i : J} (a : j ⟶ i), (sheaf i).presheaf ⟶ (D.F.map a) _* (sheaf j).presheaf)
    (hid : ∀ (j : J) (e : (Opens.map (D.F.map (𝟙 j))).op ⟶ 𝟭 (Opens (D.F.obj j))ᵒᵖ),
      push (𝟙 j) ≫ Functor.whiskerRight e (sheaf j).presheaf = 𝟙 (sheaf j).presheaf)
    (hcomp : ∀ {k j i : J} (b : k ⟶ j) (a : j ⟶ i)
      (e : (Opens.map (D.F.map (b ≫ a))).op ⟶
        (Opens.map (D.F.map a)).op ⋙ (Opens.map (D.F.map b)).op),
      push (b ≫ a) ≫ Functor.whiskerRight e (sheaf k).presheaf =
        push a ≫ (Presheaf.pushforward AddCommGrpCat.{max v u} (D.F.map a)).map (push b)) :
    D.AbelianSystem where
  sheaf := sheaf
  push := push
  push_id j V e := by
    have h := NatTrans.congr_app (hid j (D.preIdNatTrans j)) (op V)
    rw [NatTrans.comp_app, Functor.whiskerRight_app,
      Subsingleton.elim ((D.preIdNatTrans j).app (op V)) e] at h
    exact h
  push_comp b a V e := by
    have h := NatTrans.congr_app (hcomp b a (D.preCompNatTrans b a)) (op V)
    rw [NatTrans.comp_app, Functor.whiskerRight_app,
      Subsingleton.elim ((D.preCompNatTrans b a).app (op V)) e] at h
    exact h

/-! ### The single-universe statements

`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.typeSystem` is stated at
`SpectralAbelianSheafSystem.{u, u, u}` for `J : Type u`, which is the universe assignment the two
colimit-comparison clauses of Stacks 0A37 are restated at.  The statements that mention it are
therefore confined to `v = u`. -/

namespace AbelianSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : SpectralDiagram.{u, u} J}
  (A : D.AbelianSystem)

/-- The underlying `SpectralDiagram` of the comparison is `D`. -/
lemma toSpectralAbelianSheafSystem_diagram :
    A.toSpectralAbelianSheafSystem.typeSystem.diagram = D := rfl

end AbelianSystem

end SpectralDiagram

/-- Equal morphisms of presheafed spaces have equal components at an open, up to a restriction. -/
private theorem c_app_comp_map_of_hom_eq {C : Type*} [Category C] {X Y : PresheafedSpace C}
    {f g : X.Hom Y} (h : f = g) (V : Opens Y)
    (e : op ((Opens.map f.base).obj V) ⟶ op ((Opens.map g.base).obj V)) :
    f.c.app (op V) ≫ X.presheaf.map e = g.c.app (op V) := by
  rw [PresheafedSpace.congr_app h (op V), Category.assoc, X.presheaf.map_comp_map_eq_id]
  exact Category.comp_id _

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- The identity law of `S.E`, read at an open: the component of the `f`-map of `𝟙 j`, followed
by the restriction identifying `f_{𝟙}⁻¹V` with `V`, is the identity.  This is
`AlgebraicGeometry.PresheafedSpace.congr_app` applied to `S.E.map_id`, with the `eqToHom` it
produces absorbed by `TopCat.Presheaf.map_comp_map_eq_id`.

Stated in the `S.E` spelling and used by `exact`: a `rw` whose motive crosses the boundary
between `(S.E.obj j).presheaf` and `S.typeSystem.diagram.F.obj j` is refused. -/
theorem E_c_app_id (j : J) (V : Opens (S.E.obj j))
    (e : op ((Opens.map (S.E.map (𝟙 j)).hom.base).obj V) ⟶ op V) :
    (S.E.map (𝟙 j)).hom.c.app (op V) ≫ (S.E.obj j).presheaf.map e =
      𝟙 ((S.E.obj j).presheaf.obj (op V)) := by
  have hh : (S.E.map (𝟙 j)).hom = (𝟙 (S.E.obj j) : S.E.obj j ⟶ S.E.obj j).hom :=
    congrArg (fun f => f.hom) (S.E.map_id j)
  exact c_app_comp_map_of_hom_eq hh V e

/-- The cocycle law of `S.E`, read at an open.  This is
`AlgebraicGeometry.PresheafedSpace.congr_app` applied to `S.E.map_comp`, with the `eqToHom` it
produces absorbed by `TopCat.Presheaf.map_comp_map_eq_id`. -/
theorem E_c_app_comp {k j i : J} (b : k ⟶ j) (a : j ⟶ i) (V : Opens (S.E.obj i))
    (e : op ((Opens.map (S.E.map (b ≫ a)).hom.base).obj V) ⟶
      op ((Opens.map (S.E.map b).hom.base).obj ((Opens.map (S.E.map a).hom.base).obj V))) :
    (S.E.map (b ≫ a)).hom.c.app (op V) ≫ (S.E.obj k).presheaf.map e =
      (S.E.map a).hom.c.app (op V) ≫
        (S.E.map b).hom.c.app (op ((Opens.map (S.E.map a).hom.base).obj V)) := by
  have hh : (S.E.map (b ≫ a)).hom = (S.E.map b ≫ S.E.map a).hom :=
    congrArg (fun f => f.hom) (S.E.map_comp b a)
  exact c_app_comp_map_of_hom_eq hh V e

/-- **A bundled system, read as a system over its own underlying diagram of spaces.**  The
sheaves and the `f_a`-maps are the components of `S.E`, and the two laws are `E_c_app_id` and
`E_c_app_comp`, i.e. `S.E.map_id` and `S.E.map_comp` read at an open. -/
def toAbelianSystem : (S.typeSystem.diagram).AbelianSystem where
  sheaf j := ⟨(S.E.obj j).presheaf, (S.E.obj j).IsSheaf⟩
  push a := (S.E.map a).hom.c
  push_id j V e := S.E_c_app_id j V e
  push_comp b a V e := S.E_c_app_comp b a V e

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end

end
