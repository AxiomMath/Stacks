module

public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.StageOpenImmersion
public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.Localization
public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.OpensRange

/-!
# Step (ii) of the one-affine-open step: the stage of the overlap as an open of a fibre product

Let `D` be a diagram of schemes, let the sections of its stages form a cocone over a ring `R`,
let `jVY : V ⟶ Y` be an open immersion with `R` the sections of `V`, and let `g` be finitely
many sections of `Y` whose standard opens lie inside the image of `jVY`.  At a stage `j` whose
scheme `D.obj j` is quasi-affine and is covered by the affine basic opens of lifts of the
restricted `g`, the composite `D.obj j ⟶ Spec Γ(D.obj j, ⊤) ⟶ Spec (Γ(Y, ⊤) ×_R Γ(D.obj j, ⊤))`
is an open immersion.

This is the conclusion of step (ii) of the one-affine-open step of Tag 07RN.  In the argument
`Y` is the affine open being added, `V` is its overlap with the part of the scheme already
approximated, `D` is the system of models of that part, `D.obj j` is the model of the overlap at
a finite stage, and the open immersion produced here is one of the two legs along which step
(iii) glues the model of the already approximated part to the model of the affine open being
added.

## Main results

* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp_SpecMap_snd` is the assembly of the two halves
  of step (ii).  The ring half, `AlgebraicGeometry.isOpenImmersion_spec_fibreProduct_of_app_eq`
  — Tag 01Z9 applied to the cartesian square of the fibre product — gives an open immersion of
  the union of standard opens `⨆ l, D(f l)` of `Spec Γ(D.obj j, ⊤)`.  The geometric half,
  `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp`, replaces that union by the stage itself,
  using the equality of opens
  `AlgebraicGeometry.Scheme.opensRange_toSpecΓ_eq_iSup_basicOpen`.

* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp_SpecMap_snd_of_basicOpen_le` is the same
  statement with the localization hypothesis discharged geometrically, by
  `AlgebraicGeometry.bijective_awayMap_appTop_of_basicOpen_le_opensRange`: it holds as soon as
  each standard open `Y.basicOpen (g l)` lies inside the overlap.  This is the form in which the
  one-affine-open argument has its hypotheses, since the `g l` are chosen there as finitely many
  standard opens of the affine open being added which lie inside the overlap and cover it.

## Implementation notes

The ring diagram is spelled `D.op ⋙ Scheme.Γ` rather than as an abstract functor to
`CommRingCat` so that the stage ring is `Γ(D.obj j, ⊤)` on the nose.  That identification is
definitional, and it is what lets the two halves be composed with no comparison isomorphism: the
family `f` of lifts is a family of global sections of the stage, which is simultaneously what
the equality of opens is stated for and what Tag 01Z9 takes its standard opens of.  Spelling the
diagram abstractly would force an isomorphism `F.obj j ≅ Γ(D.obj j, ⊤)` into the statement and
with it the transport of the union of standard opens along its spectrum.

The index universe of the diagram is tied to the scheme universe, since the cocone of sections
is a cocone of `CommRingCat` in the scheme universe over that index category, as in Tag 06AC.
Nothing here needs the index category to be filtered or cofiltered: the stage is given, and no
colimit or limit is taken.

* The quasi-affineness of the stage is an instance argument.  It is *not* derivable from the
  other hypotheses by instance search even though it follows from them — affine basic opens
  covering a quasi-compact scheme make it quasi-affine, by
  `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` — because
  quasi-compactness of the stage is itself not among the instances here.  In the application it
  comes from Tag 01Z5, in the form
  `AlgebraicGeometry.Scheme.exists_forall_isQuasiAffine_compatibleOpens`.

* `Stacks.FibreProduct.snd` is the projection onto the *stage* ring, and it is the one whose
  spectrum receives the open immersion.  Swapping it for the first projection gives a true
  cartesian square and a false conclusion.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **Step (ii) of the one-affine-open step of Tag 07RN.**  At a quasi-affine stage of the
overlap which is covered by the affine basic opens of lifts `f` of the elements `s (g l)`, the
map to the spectrum of the fibre product `B ×_R Γ(D.obj j, ⊤)` is an open immersion.

This composes the ring half, `AlgebraicGeometry.isOpenImmersion_spec_fibreProduct_of_app_eq`,
with the geometric half, `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp`. -/
lemma isOpenImmersion_toSpecΓ_comp_SpecMap_snd {J : Type u} [Category.{u} J]
    {D : J ⥤ Scheme.{u}} {R : CommRingCat.{u}}
    (τ : D.op ⋙ Scheme.Γ ⟶ (Functor.const Jᵒᵖ).obj R) {B : CommRingCat.{u}} (s : B ⟶ R)
    (j : J) [(D.obj j).IsQuasiAffine] {n : ℕ} (g : Fin n → B) (f : Fin n → Γ(D.obj j, ⊤))
    (hf : ∀ l, τ.app (op j) (f l) = s (g l))
    (hloc : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l)))
    (haff : ∀ l, IsAffineOpen ((D.obj j).basicOpen (f l)))
    (hcov : ⨆ l, (D.obj j).basicOpen (f l) = ⊤) :
    IsOpenImmersion ((D.obj j).toSpecΓ ≫
      Spec.map (Stacks.FibreProduct.snd s (τ.app (op j)))) :=
  isOpenImmersion_toSpecΓ_comp f haff hcov _
    (isOpenImmersion_spec_fibreProduct_of_app_eq τ s g (op j) f hf hloc)

/-- **Step (ii) with the localization hypothesis discharged.**  If the `g l` are sections of the
affine open being added whose standard opens lie inside the overlap, then the localization
hypothesis of Tag 01Z9 holds by the qcqs lemma, Tag 01P7, applied twice, and the stage of the
overlap maps by an open immersion into the spectrum of the fibre product. -/
lemma isOpenImmersion_toSpecΓ_comp_SpecMap_snd_of_basicOpen_le {J : Type u} [Category.{u} J]
    {D : J ⥤ Scheme.{u}} {V Y : Scheme.{u}} (jVY : V ⟶ Y) [IsOpenImmersion jVY]
    [CompactSpace V] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (τ : D.op ⋙ Scheme.Γ ⟶ (Functor.const Jᵒᵖ).obj Γ(V, ⊤))
    (j : J) [(D.obj j).IsQuasiAffine] {n : ℕ} (g : Fin n → Γ(Y, ⊤))
    (hgle : ∀ l, Y.basicOpen (g l) ≤ jVY.opensRange) (f : Fin n → Γ(D.obj j, ⊤))
    (hf : ∀ l, τ.app (op j) (f l) = jVY.appTop (g l))
    (haff : ∀ l, IsAffineOpen ((D.obj j).basicOpen (f l)))
    (hcov : ⨆ l, (D.obj j).basicOpen (f l) = ⊤) :
    IsOpenImmersion ((D.obj j).toSpecΓ ≫
      Spec.map (Stacks.FibreProduct.snd jVY.appTop (τ.app (op j)))) :=
  isOpenImmersion_toSpecΓ_comp_SpecMap_snd τ jVY.appTop j g f hf
    (fun l ↦ bijective_awayMap_appTop_of_basicOpen_le_opensRange jVY (g l) (hgle l)) haff hcov

end AlgebraicGeometry
