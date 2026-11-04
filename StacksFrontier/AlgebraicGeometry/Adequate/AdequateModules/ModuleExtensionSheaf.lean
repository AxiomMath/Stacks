module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCoveringCofinality
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ModuleExtensionDescent
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The module extensions are sheaves on the algebras of a big site over an affine base

Let `Spec A` be affine and let `B` be a chosen big `τ`-site over it. The `A`-algebras whose
spectra belong to the site carry the topology `Stacks.Adequate.affineSubsiteTopology` induced
from the site along the affine-spectrum functor. This file proves that every module extension
`C ↦ C ⊗[A] M` is a **sheaf** for that topology.

This is the hypothesis `Stacks.Adequate.AffineModuleExtensionSheaf` of [Stacks, Tag 06VP], and
with it the last unproved input of that tag: what the source's colimit computation of the plus
construction over the standard affine `τ`-coverings of an affine amounts to.

The proof has two halves. The **algebraic** half is
`Stacks.Adequate.isSheafFor_ofArrows_siteModuleExtension'`, the sheaf condition for one finite
family of algebras of the site whose product is faithfully flat over the base, which is
[Stacks, Tag 023M]. The **geometric** half is here: every covering sieve of an algebra of the
site contains such a family. A covering sieve of the algebras pushes forward to a covering sieve
of the affine object of the site it sits over; that sieve is refined by a finite covering of the
affine object by affine objects whose morphisms are `τ`-covering morphisms
(`Stacks.Adequate.BigSite.affineCovCofinal`); each member is the spectrum of an algebra of the
site, so the refinement comes from morphisms of algebras of the site, which lie in the given
sieve because the affine-spectrum functor is fully faithful; and the product of those algebras is
faithfully flat over the base because its members are flat and jointly surjective on spectra.

## Main results

* `Module.FaithfullyFlat.pi_of_comap_surjective` — a finite product of flat algebras is
  faithfully flat as soon as every prime of the base is in the image of the spectrum of one of
  the factors. Flatness of the product is `Module.Flat.pi_of_finite`, which the development
  already has; it is reproved in one line inside the proof rather than imported, because its
  home is `StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeNilpotentSmooth` and
  nothing else here needs that file.
* `Stacks.Adequate.size_Spec_tensorProduct_lt` — the cutoff category of schemes is closed under
  the spectrum of a tensor product of two of its affine rings. Only `ℵ₀ < κ` is used.
* `Stacks.Adequate.exists_siteAlgebra_iso_of_isAffine` — an affine object of a chosen big site
  over `Spec A` is isomorphic to the spectrum of an `A`-algebra of the site.
* `Stacks.Adequate.exists_refinement_isSheafFor` — **the refinement**: every covering sieve of
  an algebra of the site contains a finite family for which every module extension satisfies the
  sheaf condition, and that family generates a covering sieve.
* `Stacks.Adequate.isSeparatedFor_siteModuleExtension` — a module extension is separated for
  every covering sieve.
* `Stacks.Adequate.isSheaf_siteModuleExtension` — **the main result**: a module extension is a
  sheaf for the induced topology on the algebras of the site.

## Implementation notes

The amalgamation produced over the refinement is shown to amalgamate the whole covering sieve by
separatedness at the *source* of each of its arrows, for the sieve the refinement generates
pulled back there — which is a covering sieve because the refinement generates one. So no base
change of the refinement, and no pullbacks in the category of algebras of the site, are needed.

The `AddCommGrpCat`-valued sheaf condition is obtained from the `Type`-valued one through
`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`, whose hypothesis on the forgetful functor is
`ReflectsLimitsOfSize` and therefore imposes no relation between the universe of the modules and
the universe of the site.

## References

* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v m

/-- A finite product of flat algebras is faithfully flat as soon as every prime of the base is
in the image of the spectrum of one of the factors. -/
public theorem Module.FaithfullyFlat.pi_of_comap_surjective {R : Type u} [CommRing R]
    {ι : Type v} [Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Flat R (S i)]
    (h : ∀ p : PrimeSpectrum R, ∃ (i : ι) (q : PrimeSpectrum (S i)),
      PrimeSpectrum.comap (algebraMap R (S i)) q = p) :
    Module.FaithfullyFlat R (∀ i, S i) := by
  have : Module.Flat R (∀ i, S i) := by
    have : Fintype ι := Fintype.ofFinite ι
    exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι S).symm
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
  obtain ⟨i, q, hq⟩ := h p
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j => S j) i) q, ?_⟩
  have he : (Pi.evalRingHom (fun j => S j) i).comp (algebraMap R (∀ j, S j))
      = algebraMap R (S i) := rfl
  rw [← PrimeSpectrum.comap_comp_apply, he, hq]

namespace Stacks.Adequate

/-- The spectrum of a tensor product of two rings whose spectra belong to the cutoff category
again belongs to it. No property of the cutoff beyond `ℵ₀ < κ` is used: the cardinality of a
tensor product is bounded by the maximum of `ℵ₀` and the cardinalities of the factors. -/
public theorem size_Spec_tensorProduct_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    (R : Type u) [CommRing R] (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hS : (Spec (CommRingCat.of S)).size < κ) (hT : (Spec (CommRingCat.of T)).size < κ) :
    (Spec (CommRingCat.of (TensorProduct R S T))).size < κ := by
  rw [Scheme.size_Spec] at hS hT ⊢
  exact max_lt hκ (lt_of_le_of_lt Cardinal.mk_tensorProduct_le
    (max_lt hκ (max_lt (max_lt_iff.mp hS).2 (max_lt_iff.mp hT).2)))

section Refinement

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- An affine object of a chosen big site over `Spec A` is the spectrum of an algebra of the
site. -/
public theorem exists_siteAlgebra_iso_of_isAffine {W : B.category} (hW : IsAffine W.left.obj) :
    ∃ Y : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff),
      Nonempty ((affineSpecOver B A (𝟙 (Spec A))).obj (op Y) ≅ W) := by
  obtain ⟨R₀, ⟨e⟩⟩ := (essImage_algSpec (G := B.toOver.obj W)).mpr hW
  have hsize : schemeSizeBelow B.cutoff (Spec (CommRingCat.of (R₀.unop : Type u))) :=
    (Scheme.size_congr ((Over.forget (Spec A)).mapIso e)).trans_lt W.left.property
  refine ⟨⟨R₀.unop, hsize⟩, ⟨?_⟩⟩
  exact Over.isoMk (ObjectProperty.isoMk _ ((Over.forget (Spec A)).mapIso e))
    (ObjectProperty.hom_ext _ ((Over.w e.hom).trans (Category.comp_id _).symm))

/-- For a fully faithful functor, an arrow whose image lies in the pushforward of a sieve lies
in the sieve. -/
public theorem arrows_of_functorPushforward {C : Type*} [Category C] {D : Type*} [Category D]
    (G : C ⥤ D) [G.Full] [G.Faithful] {X : C} (Sv : Sieve X) {Y : C} (h : Y ⟶ X)
    (hm : (Sv.functorPushforward G).arrows (G.map h)) : Sv.arrows h := by
  obtain ⟨Z, k, g, hk, he⟩ := hm
  obtain ⟨g', rfl⟩ := G.map_surjective g
  have : h = g' ≫ k := G.map_injective (by rw [he, G.map_comp])
  rw [this]
  exact Sv.downward_closed hk g'

/-- The scheme morphism underlying the image of a morphism of algebras of the site. -/
public theorem affineSpecOver_toOver_map
    {Y Y' : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ}
    (g : Y ⟶ Y') :
    (B.toOver.map ((affineSpecOver B A (𝟙 (Spec A))).map g)).left =
      Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) := rfl

/-- **Every covering sieve of the algebras of a chosen big site over an affine base contains a
finite family for which the module extensions satisfy the sheaf condition.** -/
public theorem exists_refinement_isSheafFor
    {X : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ}
    {Sv : Sieve X} (hSv : Sv ∈ affineSubsiteTopology B X) :
    ∃ R₁ : Presieve X, (∀ ⦃Z⦄ ⦃f : Z ⟶ X⦄, R₁ f → Sv.arrows f) ∧
      Sieve.generate R₁ ∈ affineSubsiteTopology B X ∧
      ∀ M : ModuleCat.{max u m} (A : Type u),
        Presieve.IsSheafFor
          ((siteModuleExtension (P := schemeSizeBelow B.cutoff) M).presheaf ⋙
            forget AddCommGrpCat.{max u m}) R₁ := by
  classical
  have hpush := Functor.mem_restrictedTopology_iff.mp hSv
  have haff : (affineSpecOver B A (𝟙 (Spec A))).obj X ∈ B.affineObjects := by
    show IsAffine (Spec (CommRingCat.of (X.unop.obj : Type u)))
    infer_instance
  obtain ⟨E, hE, hle⟩ := B.affineCovCofinal _ haff _ hpush
  obtain ⟨-, hfin, hXaff, hprop, hsurjE⟩ := hE
  choose Yalg hYalg using fun i => exists_siteAlgebra_iso_of_isAffine B (hXaff i)
  choose q hq using fun i =>
    (affineSpecOver B A (𝟙 (Spec A))).map_surjective ((hYalg i).some.hom ≫ E.1.f i)
  have hfac : ∀ i, E.1.f i =
      (hYalg i).some.inv ≫ (affineSpecOver B A (𝟙 (Spec A))).map (q i) := fun i => by
    rw [hq i, Iso.inv_hom_id_assoc]
  refine ⟨Presieve.ofArrows (fun i => op (Yalg i)) q, ?_, ?_, ?_⟩
  · rintro Z f ⟨i⟩
    refine arrows_of_functorPushforward (affineSpecOver B A (𝟙 (Spec A))) Sv (q i) ?_
    rw [hq i]
    exact (Sv.functorPushforward _).downward_closed (hle _ (E.1.sieve₀_f i)) (hYalg i).some.hom
  · refine Functor.mem_restrictedTopology_iff.mpr ?_
    refine B.topology.superset_covering ?_ E.2
    rintro Z f ⟨W, g, h, ⟨i⟩, rfl⟩
    have h1 : (Sieve.functorPushforward (affineSpecOver B A (𝟙 (Spec A)))
        (Sieve.generate (Presieve.ofArrows (fun i => op (Yalg i)) q))).arrows
          ((affineSpecOver B A (𝟙 (Spec A))).map (q i)) :=
      Presieve.image_mem_functorPushforward _ _
        ⟨_, 𝟙 _, q i, Presieve.ofArrows.mk i, (Category.id_comp _).symm⟩
    have h2 : g ≫ E.1.f i =
        (g ≫ (hYalg i).some.inv) ≫ (affineSpecOver B A (𝟙 (Spec A))).map (q i) := by
      rw [Category.assoc, ← hfac i]
    rw [h2]
    exact (Sieve.functorPushforward (affineSpecOver B A (𝟙 (Spec A)))
      (Sieve.generate (Presieve.ofArrows (fun i => op (Yalg i)) q))).downward_closed h1 _
  · intro M
    let : ∀ i, Algebra ((X.unop.obj : Type u)) (((Yalg i).obj : Type u)) :=
      fun i => arrowAlgebra (q i).unop
    have hschemeflat : ∀ i,
        Flat (B.toOver.map ((affineSpecOver B A (𝟙 (Spec A))).map (q i))).left := by
      intro i
      have hEi : Flat (B.toOver.map (E.1.f i)).left := by
        have h := hprop i
        cases τ with
        | syntomic => exact AlgebraicGeometry.flat h
        | fppf => exact h.1
        | zariski | etale | smooth => have := h; infer_instance
      rw [hq i, B.toOver.map_comp, Over.comp_left]
      have : IsIso (B.toOver.map (hYalg i).some.hom).left :=
        inferInstanceAs (IsIso ((B.toOver ⋙ Over.forget (Spec A)).map (hYalg i).some.hom))
      exact MorphismProperty.comp_mem _ _ _ inferInstance hEi
    have hmodflat : ∀ i, Module.Flat ((X.unop.obj : Type u)) (((Yalg i).obj : Type u)) := by
      intro i
      have h := hschemeflat i
      rw [affineSpecOver_toOver_map B (q i)] at h
      exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @Flat)).mp h
    have hff : Module.FaithfullyFlat ((X.unop.obj : Type u))
        (∀ i, ((Yalg i).obj : Type u)) := by
      refine Module.FaithfullyFlat.pi_of_comap_surjective _ fun p => ?_
      obtain ⟨i, y, hy⟩ := hsurjE p
      refine ⟨i, (B.toOver.map (hYalg i).some.inv).left.base y, ?_⟩
      have hkey : (B.toOver.map ((affineSpecOver B A (𝟙 (Spec A))).map (q i))).left.base
          ((B.toOver.map (hYalg i).some.inv).left.base y) = p := by
        rw [show (B.toOver.map ((affineSpecOver B A (𝟙 (Spec A))).map (q i))).left.base
              ((B.toOver.map (hYalg i).some.inv).left.base y) =
            ((B.toOver.map (hYalg i).some.inv).left ≫
              (B.toOver.map ((affineSpecOver B A (𝟙 (Spec A))).map (q i))).left).base y from rfl,
          ← Over.comp_left, ← B.toOver.map_comp, ← hfac i]
        exact hy
      rw [affineSpecOver_toOver_map B (q i)] at hkey
      exact hkey
    exact isSheafFor_ofArrows_siteModuleExtension' M (fun i => (q i).unop)
      (fun i j => size_Spec_tensorProduct_lt B.aleph0_lt_cutoff _ _ _
        (Yalg i).property (Yalg j).property) hff

/-- Separatedness of a module extension for every covering sieve of the algebras of the site:
two amalgamations of a compatible family agree already on a jointly faithfully flat finite
subfamily. -/
public theorem isSeparatedFor_siteModuleExtension (M : ModuleCat.{max u m} (A : Type u))
    {X : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ}
    {Sv : Sieve X} (hSv : Sv ∈ affineSubsiteTopology B X) :
    Presieve.IsSeparatedFor
      ((siteModuleExtension (P := schemeSizeBelow B.cutoff) M).presheaf ⋙
        forget AddCommGrpCat.{max u m}) Sv.arrows := by
  obtain ⟨R₁, hR₁le, -, hR₁sh⟩ := exists_refinement_isSheafFor B hSv
  intro x t₁ t₂ h₁ h₂
  exact (hR₁sh M).isSeparatedFor (x.restrict hR₁le) t₁ t₂ (fun {_} f hf => h₁ f (hR₁le hf))
    (fun {_} f hf => h₂ f (hR₁le hf))

/-- **The module extensions are sheaves for the topology induced on the algebras of a chosen big
site over an affine base.** -/
public theorem isSheaf_siteModuleExtension (M : ModuleCat.{max u m} (A : Type u)) :
    Presheaf.IsSheaf (affineSubsiteTopology B)
      (siteModuleExtension (P := schemeSizeBelow B.cutoff) M).presheaf := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{max u m})
    ((isSheaf_iff_isSheaf_of_type _ _).mpr ?_)
  intro X Sv hSv
  obtain ⟨R₁, hR₁le, hR₁cov, hR₁sh⟩ := exists_refinement_isSheafFor B hSv
  refine (Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor).mp
    ⟨isSeparatedFor_siteModuleExtension B M hSv, fun x hx => ?_⟩
  obtain ⟨t, ht, -⟩ := hR₁sh M (x.restrict hR₁le) (hx.restrict hR₁le)
  refine ⟨t, fun Z f hf => ?_⟩
  refine (isSeparatedFor_siteModuleExtension B M
    ((affineSubsiteTopology B).pullback_stable f hR₁cov)).ext fun W g hg => ?_
  obtain ⟨V, c, r, hr, hgf⟩ := hg
  have h1 : ∀ (a : ((siteModuleExtension (P := schemeSizeBelow B.cutoff) M).presheaf ⋙
      forget AddCommGrpCat.{max u m}).obj (op X)),
      ((siteModuleExtension (P := schemeSizeBelow B.cutoff) M).presheaf ⋙
          forget AddCommGrpCat.{max u m}).map g.op
        (((siteModuleExtension (P := schemeSizeBelow B.cutoff) M).presheaf ⋙
          forget AddCommGrpCat.{max u m}).map f.op a) =
      ((siteModuleExtension (P := schemeSizeBelow B.cutoff) M).presheaf ⋙
        forget AddCommGrpCat.{max u m}).map (c ≫ r).op a := fun a => by
    rw [hgf]
    exact (FunctorToTypes.map_comp_apply _ _ _ _).symm
  rw [h1 t, show ((c ≫ r).op : op X ⟶ op W) = r.op ≫ c.op from rfl,
    FunctorToTypes.map_comp_apply, ht r hr]
  exact (hx g c hf (hR₁le hr) hgf.symm).symm

end Refinement

end Stacks.Adequate

end
