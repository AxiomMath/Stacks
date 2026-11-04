module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Sections
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange

/-!
# Base change of a tautological datum on a projective bundle

Let `g : X ⟶ Y` be a morphism of schemes, `E` a quasi-coherent `𝒪_Y`-module, `E'` a
quasi-coherent `𝒪_X`-module and `hE : E' ≅ g^*E`. Write `π : 𝐏(E) ⟶ Y` and `π' : 𝐏(E') ⟶ X`
for the two projections and `b : 𝐏(E') ⟶ 𝐏(E)` for the base-change comparison morphism
`Stacks.RelativeProj.projectiveBundleBaseChange`, so that `b ≫ π = π' ≫ g` and the square is
cartesian.

A tautological datum on `𝐏(E)` — an invertible `𝒪(1)` together with a surjection
`π^*E ⟶ 𝒪(1)`, `Stacks.RelativeProj.TautologicalDatum` — pulls back along `b` to a tautological
datum on `𝐏(E')`, because `b^*π^*E` is canonically `π'^*E'`:

```
b^*π^*E  ≅  (b ≫ π)^*E  ≅  (π' ≫ g)^*E  ≅  π'^*(g^*E)  ≅  π'^*E'
```

That composite isomorphism is `Stacks.RelativeProj.tautologicalBaseChangeIso`, and the
base-changed datum is `Stacks.RelativeProj.TautologicalDatum.baseChange`. Tag 0B3V's clause
*the comparison morphism pulls the universal quotient back to the universal quotient* is then
the statement that the pullback of the tautological surjection along `b` agrees with the
tautological surjection of `𝐏(E')` through that isomorphism, which is here proved in the
equational form and in the existential form the tag states it in.

## Main definitions

* `Stacks.RelativeProj.tautologicalBaseChangeIso`: the canonical isomorphism
  `b^*π^*E ≅ π'^*E'`, the four-step chain displayed above.
* `Stacks.RelativeProj.TautologicalDatum.baseChange`: the tautological datum on `𝐏(E')` obtained
  by pulling one on `𝐏(E)` back along `b`.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.tautologicalBaseChangeIso_hom_comp_baseChange_univ`:
  **the universal quotient of the base-changed datum is the pullback of the universal
  quotient**, with no comparison isomorphism left over.
* `Stacks.RelativeProj.projectiveBundleBaseChange_tautological`: **Tag 0B3V's clause in its
  existential form**, for a tautological datum on `𝐏(E)`. The datum on `𝐏(E')` is the
  base-changed one and the isomorphism is the identity, so nothing is assumed beyond the datum.
* `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_of_eq` and
  `Stacks.RelativeProj.projectiveBundleBaseChangeIsoFlip_tautological`: the same statement
  written at an arbitrary morphism equal to `b`, and at the second projection of the comparison
  isomorphism `𝐏(E') ≅ X ×_Y 𝐏(E)`, which is the spelling Tag 0B3V's clause uses for it. In the
  latter the datum on `𝐏(E')` is existentially quantified, which is the closest this file gets
  to the shape of the tag's own statement.
* `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_of_iso`: the transport of that
  clause to any tautological datum on `𝐏(E')` *given* an identification of it, over `π'^*E'`,
  with the base-changed one. **It assumes an isomorphism with the asserted property and returns
  that same isomorphism**, so it is a transport lemma and not an existence statement; everything
  it adds over the equational result above is bookkeeping. It is listed last deliberately.

## Implementation notes

**`TautologicalDatum` is inhabited at every rank.**
`Stacks.RelativeProj.tautologicalDatum` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalDatumExists.lean` inhabits it for an
arbitrary quasi-coherent `E`; in rank one there are also the cheaper
`Stacks.RelativeProj.TautologicalDatum.ofInvertible` and
`Stacks.RelativeProj.tautologicalDatumUnit`. So the statements below are not vacuous at any rank.
For rank at least two the twist of a relative `Proj` *situation* is constructed on the other
substrate, and the two substrates agree over the base, so the datum exists there too. There is no
second gap either: a datum on `𝐏(E)` suffices, the one on `𝐏(E')` being produced
rather than assumed.

**What separates these statements from Tag 0B3V's clause, binder by binder.** The tag's clause
takes `g`, `E`, `E'`, the two quasi-coherence instances and `hE`, and asserts the existence of
the comparison of tautological modules for *the* universal quotient of each of the two
projective bundles. `projectiveBundleBaseChangeIsoFlip_tautological` takes those same binders
plus **one**, `D : TautologicalDatum Y E`, and existentially quantifies the datum on `𝐏(E')`.
So two things are still owed, and neither is a proof:

1. *The datum on `𝐏(E)`.* The tag has it canonically; here it is a hypothesis. It is supplied
   unconditionally for an invertible `E` by `TautologicalDatum.ofInvertible` and is open for
   rank at least two (see above).
2. *That the base-changed datum is the canonical one on `𝐏(E')`.* What is proved here is that
   the base change of a datum satisfies the tag's equation, not that it is `𝐏(E')`'s own
   universal quotient. Identifying the two in general needs the mapping-in property at **every**
   scheme over the base, whereas `TautologicalDatum.IsUniversal` is that property at the base
   alone — sections of `π'` are `X`-points of `𝐏(E)`, not `Y`-points — so `IsUniversal` is *not*
   stable under base change and cannot supply the identification. For an invertible `E` the
   identification needs no mapping-in property at all and is
   `TautologicalDatum.baseChange_ofInvertible_univ_comp_iso_hom`, with
   `projectiveBundleBaseChange_tautological_ofInvertible` the resulting clause at two canonical
   data.

Those two, together with the hypothesis `hE : E' ≅ g^*E` that
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/ProjectiveBundleBaseChange.lean` also records as an addition no tag carries, are why no
`@[stacks 0B3V]` attribute is attached here.

**Why the comparison appears as `Iso.inv` in the datum and `Iso.hom` in the statements.** The
tag writes the clause as an equation between a map out of `b^*π^*E` and a composite that starts
by comparing `b^*π^*E` with `π'^*E'`; the datum needs a map out of `π'^*E'`. The two differ by
the direction of `tautologicalBaseChangeIso`, and
`tautologicalBaseChangeIso_hom_comp_baseChange_univ` is the one place they meet — it is
`Iso.hom_inv_id_assoc`, and it is given in term mode because after `rw` the goal is no longer
type-correct at `implicit` transparency: `(D.baseChange g E E' hE).twist` and
`(Scheme.Modules.pullback b).obj D.twist` are equal only by unfolding the structure instance.

The same wall appears at all three sites where that identification is crossed, and term mode
clears it each time: `rw [Iso.hom_inv_id_assoc]` → the term `Iso.hom_inv_id_assoc _ _`;
`rw [Category.comp_id]` on a visible `f ≫ 𝟙 = f` → the term `Category.comp_id _`; and a `rw`
chain that closes `projectiveBundleBaseChange_tautological_of_iso` to a visible `a = a` and
then fails its own reducible-transparency `rfl` → a bare `rfl`.

**`projectiveBundleBaseChange_tautological_of_eq` takes the morphism as a free variable** with
its identification as a hypothesis, rather than being stated at a composite directly, so that
`subst` can move the whole statement — including the proof argument of
`Scheme.Modules.pullbackCongr`, whose type mentions the morphism — to the spelling at which it
is proved. Stating it at the composite and rewriting fails on the dependent proof argument.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The canonical identification `b^*π^*E ≅ π'^*E'`**, for `b` the base-change comparison
morphism of projective bundles. It is the pseudofunctoriality of pullback, the commutation
`b ≫ π = π' ≫ g`, that pseudofunctoriality again on the other side, and `hE`. -/
def tautologicalBaseChangeIso :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj
        ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).obj E) ≅
      (Scheme.Modules.pullback (projectiveBundleToBase X E')).obj E' :=
  (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
      (projectiveBundleToBase Y E)).app E ≪≫
    (Scheme.Modules.pullbackCongr
      (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).app E ≪≫
    ((Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).app E).symm ≪≫
    (Scheme.Modules.pullback (projectiveBundleToBase X E')).mapIso hE.symm

/-- The identification spelled out as the four-step composite, which is how Tag 0B3V's clause
writes it. -/
@[reassoc] theorem tautologicalBaseChangeIso_hom :
    (tautologicalBaseChangeIso g E E' hE).hom =
      (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
          (projectiveBundleToBase Y E)).hom.app E ≫
        (Scheme.Modules.pullbackCongr
          (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).hom.app E ≫
        (Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).inv.app E ≫
        (Scheme.Modules.pullback (projectiveBundleToBase X E')).map hE.inv := by
  simp [tautologicalBaseChangeIso]

/-- **The base change of a tautological datum along the comparison morphism of projective
bundles.** Its twist is `b^*𝒪(1)`, invertible because pullback of sheaves of modules preserves
invertibility, and its universal surjection is the pullback of the given one, read out of
`π'^*E'` through `tautologicalBaseChangeIso`. -/
def TautologicalDatum.baseChange (D : TautologicalDatum Y E) : TautologicalDatum X E' where
  twist := (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj D.twist
  invertible :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@Stacks.Modules.isInvertible_pullback _ _ (projectiveBundleBaseChange g E E' hE) D.twist
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr D.invertible))
  univ := (tautologicalBaseChangeIso g E E' hE).inv ≫
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map D.univ
  epi_univ := by
    have := D.epi_univ
    infer_instance

/-- The twist of the base-changed datum is the pullback `b^*` of the given twist. -/
@[simp] theorem TautologicalDatum.baseChange_twist (D : TautologicalDatum Y E) :
    (D.baseChange g E E' hE).twist =
      (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj D.twist :=
  rfl

/-- The universal surjection of the base-changed datum is the pullback `b^*` of the given one,
precomposed with the inverse of `tautologicalBaseChangeIso`. -/
@[simp] theorem TautologicalDatum.baseChange_univ (D : TautologicalDatum Y E) :
    (D.baseChange g E E' hE).univ = (tautologicalBaseChangeIso g E E' hE).inv ≫
      (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map D.univ :=
  rfl

/-- **The universal quotient of the base-changed datum is the pullback of the universal
quotient**, with no comparison left over: composing it with the canonical identification of
`b^*π^*E` with `π'^*E'` gives `b^*` of the given surjection on the nose. -/
theorem TautologicalDatum.tautologicalBaseChangeIso_hom_comp_baseChange_univ
    (D : TautologicalDatum Y E) :
    (tautologicalBaseChangeIso g E E' hE).hom ≫ (D.baseChange g E E' hE).univ =
      (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map D.univ :=
  Iso.hom_inv_id_assoc _ _

/-- **Transport of the clause below to a tautological datum on `𝐏(E')` identified over
`π'^*E'` with the base change of one on `𝐏(E)`.**

This is *not* an existence statement: the isomorphism it produces is the isomorphism `β` it is
given, so its content is the equation and nothing else. The existence lies in
`projectiveBundleBaseChange_tautological`, which supplies the datum and the isomorphism, and
the content lies in `TautologicalDatum.tautologicalBaseChangeIso_hom_comp_baseChange_univ`,
which is an equation with no isomorphism at all. This exists only so that a consumer holding
its own datum on `𝐏(E')` need not re-derive the composite. -/
theorem projectiveBundleBaseChange_tautological_of_iso (D : TautologicalDatum Y E)
    (D' : TautologicalDatum X E')
    (β : (D.baseChange g E E' hE).twist ≅ D'.twist)
    (hβ : (D.baseChange g E E' hE).univ ≫ β.hom = D'.univ) :
    ∃ α : (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj D.twist ≅
        D'.twist,
      (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map D.univ ≫ α.hom =
        (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
            (projectiveBundleToBase Y E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X E')).map hE.inv ≫ D'.univ := by
  refine ⟨β, ?_⟩
  rw [← tautologicalBaseChangeIso_hom_assoc, ← hβ, ← Category.assoc,
    TautologicalDatum.tautologicalBaseChangeIso_hom_comp_baseChange_univ]
  rfl

/-- **Tag 0B3V's clause on the universal quotient of the base-change comparison**, for a
tautological datum on `𝐏(E)`: the pullback of its universal quotient along `b` *is* the
universal quotient of the base-changed datum, through the canonical identification of
`b^*π^*E` with `π'^*E'`.

Nothing is assumed beyond the datum on `𝐏(E)` — the datum on `𝐏(E')` and the comparison of
tautological modules are both produced, the latter as the identity — and the proof is the
equation `TautologicalDatum.tautologicalBaseChangeIso_hom_comp_baseChange_univ` directly, not
the transport lemma above. -/
theorem projectiveBundleBaseChange_tautological (D : TautologicalDatum Y E) :
    ∃ α : (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj D.twist ≅
        (D.baseChange g E E' hE).twist,
      (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map D.univ ≫ α.hom =
        (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
            (projectiveBundleToBase Y E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X E')).map hE.inv ≫
          (D.baseChange g E E' hE).univ := by
  refine ⟨Iso.refl _, ?_⟩
  rw [← tautologicalBaseChangeIso_hom_assoc,
    TautologicalDatum.tautologicalBaseChangeIso_hom_comp_baseChange_univ]
  exact Category.comp_id _

/-- **Tag 0B3V's clause at an arbitrary morphism equal to the comparison**, so that a consumer
holding `b` in another spelling — in particular as a projection of the comparison isomorphism —
can use it. The tautological datum on `𝐏(E')` is produced, not assumed. -/
theorem projectiveBundleBaseChange_tautological_of_eq
    (b : projectiveBundle X E' ⟶ projectiveBundle Y E)
    (hb0 : projectiveBundleBaseChange g E E' hE = b)
    (hb : b ≫ projectiveBundleToBase Y E = projectiveBundleToBase X E' ≫ g)
    (D : TautologicalDatum Y E) :
    ∃ (D' : TautologicalDatum X E') (α : (Scheme.Modules.pullback b).obj D.twist ≅ D'.twist),
      (Scheme.Modules.pullback b).map D.univ ≫ α.hom =
        (Scheme.Modules.pullbackComp b (projectiveBundleToBase Y E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr hb).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X E')).map hE.inv ≫ D'.univ := by
  subst hb0
  exact ⟨D.baseChange g E E' hE, projectiveBundleBaseChange_tautological g E E' hE D⟩

/-- **Tag 0B3V's clause at the second projection of the comparison isomorphism**
`𝐏(E') ≅ X ×_Y 𝐏(E)`, which is the morphism the tag names. Its commutation with the two
projections is
`projectiveBundleBaseChangeIsoFlip_hom_snd_comp_projectiveBundleToBase`. -/
theorem projectiveBundleBaseChangeIsoFlip_tautological (D : TautologicalDatum Y E) :
    ∃ (D' : TautologicalDatum X E')
      (α : (Scheme.Modules.pullback ((projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
        pullback.snd g (projectiveBundleToBase Y E))).obj D.twist ≅ D'.twist),
      (Scheme.Modules.pullback ((projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
            pullback.snd g (projectiveBundleToBase Y E))).map D.univ ≫ α.hom =
        (Scheme.Modules.pullbackComp ((projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
              pullback.snd g (projectiveBundleToBase Y E))
            (projectiveBundleToBase Y E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChangeIsoFlip_hom_snd_comp_projectiveBundleToBase
              g E E' hE)).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X E')).map hE.inv ≫ D'.univ :=
  projectiveBundleBaseChange_tautological_of_eq g E E' hE _
    (projectiveBundleBaseChangeIsoFlip_hom_snd g E E' hE).symm _ D

end Stacks.RelativeProj

end
