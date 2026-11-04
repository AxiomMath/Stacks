module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatCartesianFppfDescent

/-!
# The cartesian property over flat arrows descends along fppf coverings, at large module universes

This is `AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_flat_of_goodCover` for a
presheaf of modules whose sections lie in the universe `max (u + 1) v w m`, above the universe of
the structure sheaf: the universe in which the faithful `LQCoh^fbc` is characterized by the
cartesian property over flat arrows between objects over affine schemes
(`AlgebraicGeometry.Stack.IsCartesianOnFlatAffineArrows`), and in which Stacks 07AV, 07BC and
07BE live (module universe `u + 1` on an algebraic stack). The argument is the same: refine a
covering of the target by good objects to a finite flat covering on the affine subcategory, use
the fppf sheaf condition there and along its base change, and assemble with
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover`, which holds at every module
universe above the rings.

## Main results

* `AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_flat_of_goodCover_freeModuleUniverse`

## References

* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

open AffineCategory in
/-- **The cartesian property over flat arrows between affine objects descends from a class of
objects covering `𝒳` for the fppf topology**, at module universe `max (u + 1) v w m`. If `F` is an
fppf sheaf of `𝒪_𝒳`-modules, the class `good` is closed under precomposition and covers every
object for the fppf topology, and `F` is cartesian over the flat arrows between affine objects
whose target is good, then `F` is cartesian over every arrow lying over a flat morphism of affine
schemes. -/
theorem bijective_restrictionBaseChange_of_flat_of_goodCover_freeModuleUniverse
    (F : PresheafOfModules.{max (u + 1) v w m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf) F.presheaf)
    (good : 𝒳 → Prop) (hgood : ∀ ⦃z y : 𝒳⦄ (_ : z ⟶ y), good y → good z)
    (hcov : ∀ x : 𝒳, ∃ R : Sieve x, R ∈ BigFppfOver.associatedTopology B S hS p .fppf x ∧
      ∀ ⦃z : 𝒳⦄ (g : z ⟶ x), R g → good z)
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂), good x₂ →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
      Flat (B.inclusion.map (p.map e).left) →
      Function.Bijective
        (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, max (u + 1) v w m}
          (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
          F
          e.op))
    {x₁ x₂ : 𝒳} (e : x₁ ⟶ x₂)
    (h₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)))
    (h₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)))
    (hflat : Flat (B.inclusion.map (p.map e).left)) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F
      e.op) := by
  classical
  have := AffineCategory.hasPullbacks B S hS p hp
  have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := Functor.IsDenseSubsite.isCoverDense
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
    (BigFppfOver.associatedTopology B S hS p .fppf) (AffineCategory.inclusion B S hS p)
  let a₁ : AffineCategory B S hS p := ⟨x₁, h₁⟩
  let a₂ : AffineCategory B S hS p := ⟨x₂, h₂⟩
  let f : a₁ ⟶ a₂ := ObjectProperty.homMk e
  let M : PresheafOfModules.{max (u + 1) v w m} (affineStructurePresheaf B S hS p) :=
    (PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj F
  let R := affineStructureCommPresheaf B S hS p
  have hM : Presheaf.IsSheaf (associatedAffineTopology B S hS p
      (BigAffineFppf.siteKindTopology B S hS .fppf)) M.presheaf :=
    Functor.op_comp_isSheaf_of_isSheaf _ _ (BigFppfOver.associatedTopology B S hS p .fppf)
      F.presheaf hF
  have hsT : Presieve.IsSheaf (associatedAffineTopology B S hS p
      (BigAffineFppf.siteKindTopology B S hS .fppf)) (M.presheaf ⋙ forget AddCommGrpCat) :=
    Stacks.SheafOfModules.ChangeOfRings.isSheafOfTypes_of_isSheaf M.presheaf hM
  -- the sieve of arrows into `a₂` out of good affine objects covers `a₂`
  let T : Sieve a₂ :=
    { arrows := fun b _ => good b.obj
      downward_closed := fun {_ _ _} hb k => hgood k.hom hb }
  have hT : T ∈ associatedAffineTopology B S hS p
      (BigAffineFppf.siteKindTopology B S hS .fppf) a₂ := by
    rw [← Functor.functorPushforward_mem_iff (G := AffineCategory.inclusion B S hS p)
      (J := associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
      (K := BigFppfOver.associatedTopology B S hS p .fppf)]
    obtain ⟨R, hR, hRgood⟩ := hcov x₂
    refine (BigFppfOver.associatedTopology B S hS p .fppf).transitive hR _ ?_
    intro z g hg
    refine (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering ?_
      (Functor.is_cover_of_isCoverDense (AffineCategory.inclusion B S hS p)
        (BigFppfOver.associatedTopology B S hS p .fppf) z)
    rintro w k ⟨⟨b, lift, map, fac⟩⟩
    refine ⟨b, (ObjectProperty.homMk (map ≫ g) : b ⟶ a₂), lift, hgood map (hRgood g hg), ?_⟩
    rw [← fac, Category.assoc]
    rfl
  obtain ⟨E, hfin, -, hEcov, hEle⟩ := exists_finite_flat_covering B S hS p hp .fppf T hT
  have := hfin
  have hEgood : ∀ i, good (E.X i).obj := fun i => hEle _ (Sieve.ofArrows_mk _ _ i)
  have hcoverU : Sieve.ofArrows (fun i => pullback f (E.f i))
      (fun i => pullback.fst f (E.f i)) ∈ associatedAffineTopology B S hS p
        (BigAffineFppf.siteKindTopology B S hS .fppf) a₁ := by
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.pullback_stable _ f hEcov)
    intro Z h hh
    obtain ⟨Y, g₁, g₂, ⟨i⟩, hg⟩ := hh
    have hmem := (Sieve.ofArrows (fun i => pullback f (E.f i))
        (fun i => pullback.fst f (E.f i))).downward_closed
      (Sieve.ofArrows_mk (fun i => pullback f (E.f i)) (fun i => pullback.fst f (E.f i)) i)
      (pullback.lift h g₁ hg.symm)
    rwa [pullback.lift_fst] at hmem
  have := AffineCategory.preservesPullbacks_toScheme B S hS p hp
  have hflatb : ∀ {X Y Z : AffineCategory B S hS p} (u : X ⟶ Y) (v : Z ⟶ Y),
      Flat ((toScheme B S hS p).map u) → Flat ((toScheme B S hS p).map (pullback.snd u v)) :=
    fun u v hu => MorphismProperty.of_isPullback (P := @Flat)
      ((IsPullback.of_hasPullback u v).map (toScheme B S hS p)) hu
  have hcartA : ∀ {X Y : AffineCategory B S hS p} (k : X ⟶ Y), good Y.obj →
      Flat ((toScheme B S hS p).map k) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, max (u + 1) v w m}
        (R := R) M k.op) :=
    fun {X Y} k hY hk => (ConcreteCategory.isIso_iff_bijective
      (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, max (u + 1) v w m}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F
        k.hom.op)).2 (hcart k.hom hY X.property Y.property hk)
  have hiso := Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover M f E.X E.f
    (AffineCategory.flat_map_of_flat B S hS p R rfl f hflat)
    ((Presieve.isSheafFor_iff_generate _).mpr (hsT _ hEcov))
    ((Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcoverU))
    (fun i => AffineCategory.isPushout_map B S hS p R rfl hp (IsPullback.of_hasPullback f (E.f i)))
    (fun c => AffineCategory.isPushout_map B S hS p R rfl hp (IsPullback.of_hasPullback f _))
    (fun i => hcartA _ (hEgood i) (hflatb _ _ hflat))
    (fun c => hcartA _ (hgood (pullback.fst (E.f c.1) (E.f c.2)).hom (hEgood c.1))
      (hflatb _ _ hflat))
  exact (ConcreteCategory.isIso_iff_bijective _).1 hiso

end AlgebraicGeometry.Stack
