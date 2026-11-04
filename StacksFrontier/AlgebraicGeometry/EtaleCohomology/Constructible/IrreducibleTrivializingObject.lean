module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSubsheafEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves

/-!
# An irreducible trivializing object of the small étale site

On an irreducible locally Noetherian scheme `Z'` of a big étale site, a sheaf of `Λ`-modules
which is locally constant of finite type becomes constant, with finitely generated value, on an
object of the small étale site of `Z'` whose underlying scheme is *irreducible*.

Irreducibility of the trivializing object is what the argument of Stacks 09BG asks for, and it
is obtained in two steps. Local constancy at the final object supplies a covering on each member
of which the sheaf is constant; a covering sieve of the small étale site is jointly surjective
(`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`), so some member is nonempty, and a
nonempty member has a nonempty irreducible open subobject
(`AlgebraicGeometry.SmallEtale.exists_irreducibleSpace_openObj`). Constancy descends to that
subobject because it descends along any morphism of the site,
`Stacks.ConstantSheaf.constantIsoOverPullbackOfMap`.

## Main results

* `AlgebraicGeometry.exists_irreducible_trivializing_object` — the statement above.

## Implementation notes

The trivialization is recorded in the shape the definition of
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant` uses, namely an isomorphism of the constant
sheaf on the localized site at the object with the restriction of the sheaf there; the
translation to the small étale site of the object itself is
`AlgebraicGeometry.nonempty_constantSheafIso_over_iff`.

No `@[stacks]` attribute appears here: this is a step of the proof of Stacks 09BH (3), not a
numbered statement of the source.

## References

* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]

omit [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
/-- **A trivializing irreducible étale neighbourhood.** On an irreducible locally Noetherian
scheme a sheaf locally constant of finite type is constant, with finitely generated value, on an
object of the small étale site whose underlying scheme is irreducible. -/
theorem exists_irreducible_trivializing_object (Z' : B.Scheme) [IrreducibleSpace Z'.obj]
    [IsLocallyNoetherian Z'.obj]
    (F : Sheaf (SmallEtale.topology B Z'.obj Z'.property) (ModuleCat.{u + 1} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B Z'.obj Z'.property) F) :
    ∃ (V₀ : SmallEtale B Z'.obj Z'.property) (E : ModuleCat.{u + 1} Λ),
      IrreducibleSpace ((SmallEtale.toScheme B Z'.obj Z'.property).obj V₀) ∧
        ModuleCat.isFG Λ E ∧
        Nonempty ((constantSheaf ((SmallEtale.topology B Z'.obj Z'.property).over V₀)
            (ModuleCat.{u + 1} Λ)).obj E ≅
          ((SmallEtale.topology B Z'.obj Z'.property).overPullback
            (ModuleCat.{u + 1} Λ) V₀).obj F) := by
  obtain ⟨I, V, f, hcov, hc⟩ := hF (SmallEtale.final B Z'.obj Z'.property)
  obtain ⟨z⟩ := (inferInstance : IrreducibleSpace Z'.obj).toNonempty
  obtain ⟨W₁, g₁, hg₁, hz⟩ :=
    SmallEtale.exists_mem_arrows_mem_range B Z'.obj Z'.property hcov
      (show (SmallEtale.toScheme B Z'.obj Z'.property).obj
        (SmallEtale.final B Z'.obj Z'.property) from z)
  obtain ⟨w, -⟩ := hz
  obtain ⟨a, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg₁
  obtain ⟨E, hE, ⟨c⟩⟩ := hc a
  obtain ⟨W', hW'c, hW'irr⟩ :=
    SmallEtale.exists_irreducibleSpace_openObj B Z'.obj Z'.property W₁ w
  refine ⟨SmallEtale.openObj W₁ W' hW'c, E, hW'irr, hE,
    ⟨Stacks.ConstantSheaf.constantIsoOverPullbackOfMap _ (ModuleCat.{u + 1} Λ)
      (SmallEtale.openObjHom W₁ W' hW'c) F E
      (Stacks.ConstantSheaf.constantIsoOverPullbackOfMap _ (ModuleCat.{u + 1} Λ) h F E c)⟩⟩

end AlgebraicGeometry

end
