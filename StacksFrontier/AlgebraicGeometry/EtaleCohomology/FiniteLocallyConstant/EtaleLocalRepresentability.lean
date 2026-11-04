module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteConstantRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.CoverCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves

/-!
# A finite locally constant sheaf is étale-locally representable by a finite étale scheme

Let `B` be a big étale site and `X` an object of it. A finite locally constant sheaf of sets `F`
on the small étale site of `X` admits, over every object `V` of that site, a covering
`{Y i ⟶ V}` such that for each `i` the inverse image of `F` along the structure morphism of
`Y i` is representable by an object of the small étale site of the scheme `Y i` whose structure
morphism is finite. Together with effective descent of such representability along étale
coverings, a sheaf of sets on the small étale site of `X` is finite locally constant if and only
if it is represented by a scheme finite étale over `X`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability`: a sheaf whose inverse
  images along the members of a covering of `X` are representable by finite étale schemes is
  itself so representable.

## Main results

* `Stacks.EtaleCohomology.exists_cover_finiteEtaleRepresentable_of_isFiniteLocallyConstant`:
  over every object of the small étale site, a finite locally constant sheaf has a covering on
  each member of which it is representable by a finite étale scheme.
* `Stacks.EtaleCohomology.exists_cover_finiteEtaleRepresentable_final`: the same over `X`
  itself.
* `Stacks.EtaleCohomology.exists_sliceRepresentative_of_sheafPullback`: a representative of the
  inverse image of a sheaf along `V` is a representative of its restriction to the slice over `V`.
* `Stacks.EtaleCohomology.etaleDescentForFiniteEtaleRepresentability`: the descent statement
  holds in every big étale site.
* `Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent`: a
  sheaf of sets on the small étale site of `X` is finite locally constant if and only if it is
  represented by a scheme finite étale over `X`.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-! ### Étale-local representability -/

/-- Over every object `V` of the small étale site of `X` a finite locally constant sheaf of sets
`F` has a covering `{Y i ⟶ V}` on each member of which the inverse image of `F` is representable
by an object of the small étale site of `Y i` with finite structure morphism. -/
public theorem exists_cover_finiteEtaleRepresentable_of_isFiniteLocallyConstant
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.property) F]
    (V : SmallEtale B X.1 X.property) :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B X.1 X.property) (f : ∀ i, Y i ⟶ V),
      Sieve.ofArrows Y f ∈ SmallEtale.topology B X.1 X.property V ∧
        ∀ i, ∃ U : SmallEtale B (Y i).obj.left.1 (Y i).obj.left.property,
          IsFinite (B.inclusion.map U.obj.hom) ∧
            Nonempty (((smallEtaleBaseChange B (Y i).obj.hom).sheafPullback (Type (u + 1))
                (SmallEtale.topology B X.1 X.property)
                (SmallEtale.topology B (Y i).obj.left.1 (Y i).obj.left.property)).obj F ≅
              (Sheaf.sheafifiedYoneda
                (SmallEtale.topology B (Y i).obj.left.1 (Y i).obj.left.property)).obj U) := by
  obtain ⟨I, Y, f, hcov, hconst⟩ :=
    ‹Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.property)
      F›.exists_finite_cover V
  refine ⟨I, Y, f, hcov, fun i ↦ ?_⟩
  obtain ⟨E, hE, hiso⟩ := hconst i
  exact exists_finiteEtaleRepresentable_of_isConstant B _ _
    ⟨E, hE, (nonempty_constantSheafIso_over_iff B X.1 X.property (Y i) _ F E).mp hiso⟩

/-- A finite locally constant sheaf of sets `F` on the small étale site of `X` has a covering
`{Y i ⟶ X}` of the final object on each member of which the inverse image of `F` is
representable by an object of the small étale site of `Y i` with finite structure morphism. -/
public theorem exists_cover_finiteEtaleRepresentable_final
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.property) F] :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B X.1 X.property)
      (f : ∀ i, Y i ⟶ SmallEtale.final B X.1 X.property),
      Sieve.ofArrows Y f ∈
          SmallEtale.topology B X.1 X.property (SmallEtale.final B X.1 X.property) ∧
        ∀ i, ∃ U : SmallEtale B (Y i).obj.left.1 (Y i).obj.left.property,
          IsFinite (B.inclusion.map U.obj.hom) ∧
            Nonempty (((smallEtaleBaseChange B (Y i).obj.hom).sheafPullback (Type (u + 1))
                (SmallEtale.topology B X.1 X.property)
                (SmallEtale.topology B (Y i).obj.left.1 (Y i).obj.left.property)).obj F ≅
              (Sheaf.sheafifiedYoneda
                (SmallEtale.topology B (Y i).obj.left.1 (Y i).obj.left.property)).obj U) :=
  exists_cover_finiteEtaleRepresentable_of_isFiniteLocallyConstant B X F
    (SmallEtale.final B X.1 X.property)

/-! ### Effective descent of representability -/

/-- Effective descent of representability by a finite étale scheme along an étale covering, for
the small étale sites inside a fixed big étale site `B`: if the inverse images of a sheaf of sets
along the members of a covering of `X` are representable by objects of their small étale sites
with finite structure morphisms, then the sheaf is so representable over `X`. -/
public def EtaleDescentForFiniteEtaleRepresentability (B : AlgebraicGeometry.BigEtaleSite.{u}) :
    Prop :=
  ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (I : Type (u + 1)) (Y : I → SmallEtale B X.1 X.property)
    (f : ∀ i, Y i ⟶ SmallEtale.final B X.1 X.property),
    Sieve.ofArrows Y f ∈
        SmallEtale.topology B X.1 X.property (SmallEtale.final B X.1 X.property) →
      (∀ i, ∃ U : SmallEtale B (Y i).obj.left.1 (Y i).obj.left.property,
        IsFinite (B.inclusion.map U.obj.hom) ∧
          Nonempty (((smallEtaleBaseChange B (Y i).obj.hom).sheafPullback (Type (u + 1))
              (SmallEtale.topology B X.1 X.property)
              (SmallEtale.topology B (Y i).obj.left.1 (Y i).obj.left.property)).obj F ≅
            (Sheaf.sheafifiedYoneda
              (SmallEtale.topology B (Y i).obj.left.1 (Y i).obj.left.property)).obj U)) →
      ∃ U : SmallEtale B X.1 X.property, IsFinite (B.inclusion.map U.obj.hom) ∧
        Nonempty (F ≅ (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).obj U)

/-- If the inverse image of `F` along the structure morphism of an object `V` of the small étale
site of `X` is represented by an object `U` of the small étale site of `V` with finite structure
morphism, then the restriction of `F` to the localized site at `V` is represented by an object of
the slice `Over V` whose structure morphism is finite étale. -/
public theorem exists_sliceRepresentative_of_sheafPullback
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (V : SmallEtale B X.1 X.property)
    (h : ∃ U : SmallEtale B V.obj.left.1 V.obj.left.property,
      IsFinite (B.inclusion.map U.obj.hom) ∧
        Nonempty (((smallEtaleBaseChange B V.obj.hom).sheafPullback (Type (u + 1))
            (SmallEtale.topology B X.1 X.property)
            (SmallEtale.topology B V.obj.left.1 V.obj.left.property)).obj F ≅
          (Sheaf.sheafifiedYoneda
            (SmallEtale.topology B V.obj.left.1 V.obj.left.property)).obj U)) :
    ∃ A : Over V,
      IsFinite ((smallEtaleToOver B X).map A.hom).left ∧
        Etale ((smallEtaleToOver B X).map A.hom).left ∧
        Nonempty (F.over V ≅
          ((SmallEtale.topology B X.1 X.property).over V).uliftYoneda.{u + 1}.obj A) := by
  obtain ⟨U, hU, ⟨eU⟩⟩ := h
  let e := smallEtaleEquivalenceOver B X.1 X.property V
  let JV := SmallEtale.topology B V.obj.left.1 V.obj.left.property
  let K := (SmallEtale.topology B X.1 X.property).over V
  let cg := e.sheafCongr JV K (Type (u + 1))
  have hrestr : cg.inverse.obj (F.over V) ≅
      ((smallEtaleBaseChange B V.obj.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B X.1 X.property) JV).obj F :=
    ((smallEtaleSheafPullbackIsoPostcompose B X.1 X.property V (Type (u + 1))).app F).symm
  have hy : cg.inverse.obj (K.uliftYoneda.{u + 1}.obj (e.functor.obj U)) ≅
      JV.uliftYoneda.{u + 1}.obj U :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (restrictedUliftYonedaIso e.functor U)
  exact ⟨e.functor.obj U, hU, U.property, ⟨cg.inverse.preimageIso
    (hrestr ≪≫ eU ≪≫ sheafifiedYonedaIsoUliftYoneda JV U ≪≫ hy.symm)⟩⟩

/-- Effective descent of representability by a finite étale scheme along an étale covering,
`Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability`, holds in every big étale
site. -/
public theorem etaleDescentForFiniteEtaleRepresentability
    (B : AlgebraicGeometry.BigEtaleSite.{u}) : EtaleDescentForFiniteEtaleRepresentability B := by
  intro X F I Y f hcov hrep
  choose A hAfin hAet he using fun i ↦
    exists_sliceRepresentative_of_sheafPullback B X F (Y i) (hrep i)
  exact exists_finiteEtaleRepresentable_of_sliceRepresentatives B X F Y f hcov A hAfin hAet
    (fun i ↦ (he i).some)

/-- A sheaf of sets on the small étale site of `X` is finite locally constant if and only if it is
represented by an object of the site whose structure morphism is finite, that is, by a scheme
finite étale over `X`. It takes a binder `hdesc : EtaleDescentForFiniteEtaleRepresentability B`,
which defaults to the theorem `Stacks.EtaleCohomology.etaleDescentForFiniteEtaleRepresentability`,
so the statement applies to `B X F` alone. -/
@[stacks 03RV]
public theorem isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (hdesc : EtaleDescentForFiniteEtaleRepresentability B :=
      etaleDescentForFiniteEtaleRepresentability B) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.property) F ↔
      ∃ U : SmallEtale B X.1 X.property,
        IsFinite (B.inclusion.map U.obj.hom) ∧
          Nonempty (F ≅
            (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).obj U) := by
  refine ⟨fun hF ↦ ?_, isFiniteLocallyConstant_of_finiteEtaleRepresentable B X F⟩
  obtain ⟨I, Y, f, hcov, hrep⟩ := exists_cover_finiteEtaleRepresentable_final B X F
  exact hdesc X F I Y f hcov hrep

end Stacks.EtaleCohomology

end
