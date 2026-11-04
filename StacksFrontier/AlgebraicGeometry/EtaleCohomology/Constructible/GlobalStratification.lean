module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationGlue
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 095E: constructibility is one global stratification

On a quasi-compact quasi-separated scheme a stratified sheaf — a sheaf admitting, on every affine
open, a finite partition by constructible locally closed subschemes on each of which it satisfies
a given condition — admits **one** such partition of the whole scheme, and conversely. This is
the equivalence of parts (1) and (3) of Tag 095E, for sheaves of sets, of abelian groups and of
modules over a Noetherian ring at once.

The two directions are the two operations on constructible stratifications:

* **(1) implies (3).** A quasi-compact scheme is covered by finitely many affine opens; each
  carries a stratification by hypothesis, and
  `AlgebraicGeometry.exists_constructibleStratification_of_cover` glues them, cutting the strata
  of the `j`-th affine open down to the part outside the earlier ones. Quasi-separatedness is
  what makes the quasi-compact opens retrocompact, hence constructible.
* **(3) implies (1).** Restrict the global stratification to each affine open with
  `AlgebraicGeometry.exists_constructibleStratification_restrict`.

The condition on the strata has to be stable under isomorphism of sheaves *and under inverse
image along a morphism of the big étale site*, since a cut stratum is built over the original
stratum and the condition is carried to it by inverse image. For finite local constancy and for
local constancy of finite type that stability is
`AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback'` and
`AlgebraicGeometry.isFiniteTypeLocallyConstant_smallEtaleSheafPullback`.

## Main results

* `AlgebraicGeometry.exists_stratification_top_of_isStratifiedSheaf` and
  `AlgebraicGeometry.isStratifiedSheaf_of_exists_stratification_top` — the two directions for an
  arbitrary condition on the strata.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_iff_exists_stratification` — **Tag 095E for sets
  and abelian groups, the equivalence of (1) and (3).**
* `AlgebraicGeometry.isConstructibleModuleSheaf_iff_exists_stratification` — **Tag 095E for
  modules, the equivalence of (1) and (3).**

## Implementation notes

The two statements are stated with the coefficient universe of
`AlgebraicGeometry.IsConstructibleFiniteSheaf`, which is independent of the scheme universe,
rather than with the scheme-dependent one; they therefore imply the source's statement by
instantiation.

Tag 095E has four assertions — the equivalence of (1) with (2) and with (3), each for sheaves with
concrete values and for sheaves of modules — and only the two involving (3) are proved here; their
`@[stacks 095E]` attributes name which. The equivalence of (1) and (2), Zariski locality, is not:
its non-trivial direction needs the strata of a stratification of an affine open of a member of the
cover transported into the ambient scheme, which is a further operation on stratifications.

## References

* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe v w t r u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (X : B.Scheme)

/-- **Tag 095E, (1) implies (3), for an arbitrary condition on the strata.** On a quasi-compact
quasi-separated scheme a stratified sheaf admits one stratification of the whole scheme. -/
public theorem exists_stratification_top_of_isStratifiedSheaf
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    (hF : IsStratifiedSheaf B X P F) :
    ∃ t : ConstructibleStratification B X ⊤,
      ∀ i, P (t.piece i) (smallEtalePullObj B (t.inclusion i) F) := by
  classical
  have hbasis : (Set.univ : Set X.obj) ⊆ ⋃ V : X.obj.affineOpens, (V.1 : Set X.obj) := fun x _ =>
    Set.mem_iUnion.mpr (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X.obj).ge (TopologicalSpace.Opens.mem_top x)))
  obtain ⟨tf, htf⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.obj.affineOpens => (V.1 : Set X.obj)) (fun V => V.1.2) hbasis
  refine exists_constructibleStratification_of_cover B X P hPIso hPPull F ⊤
    (O := fun a : Fin tf.card => ((tf.equivFin.symm a).1 : X.obj.affineOpens).1)
    (fun a => ((tf.equivFin.symm a).1).2.isCompact) (fun a => by simp) ?_
    (fun a => (hF ((tf.equivFin.symm a).1)).choose)
    (fun a => (hF ((tf.equivFin.symm a).1)).choose_spec)
  refine Set.Subset.antisymm (fun x _ => ?_) (fun x _ => by simp)
  obtain ⟨V, hVtf, hxV⟩ := Set.mem_iUnion₂.mp (htf (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨tf.equivFin ⟨V, hVtf⟩, by rwa [Equiv.symm_apply_apply]⟩

/-- **Tag 095E, (3) implies (1), for an arbitrary condition on the strata.** A stratification of
the whole scheme restricts to every affine open. -/
public theorem isStratifiedSheaf_of_exists_stratification_top
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    (h : ∃ t : ConstructibleStratification B X ⊤,
      ∀ i, P (t.piece i) (smallEtalePullObj B (t.inclusion i) F)) :
    IsStratifiedSheaf B X P F := fun V =>
  h.elim fun t ht => exists_constructibleStratification_restrict B X P hPIso hPPull F V.1 t ht

end AlgebraicGeometry

namespace AlgebraicGeometry

section Finite

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
  {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

/-- **Stacks 095E, sets and abelian groups: the equivalence of (1) and (3).** On a quasi-compact
quasi-separated scheme, a sheaf with values in a concrete category is constructible exactly when
there is one finite partition of the whole scheme by constructible locally closed subschemes on
each of which its inverse image is finite locally constant. -/
@[stacks 095E "finite sheaves, stratification", sga "4 IX 2.4" "(i)"]
public theorem isConstructibleFiniteSheaf_iff_exists_stratification
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) :
    IsConstructibleFiniteSheaf B X F ↔
      ∃ s : ConstructibleStratification B X ⊤,
        ∀ i, Stacks.ConstantSheaf.IsFiniteLocallyConstant
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
          (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F) := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) D}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) G := fun T F G e h =>
    Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) e (hF := h)
  have hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T'.obj T'.property) (smallEtalePullObj B q G) := fun T' T q G h =>
    isFiniteLocallyConstant_smallEtaleSheafPullback' B D q G (hH := h)
  exact ⟨exists_stratification_top_of_isStratifiedSheaf B X _ hPIso hPPull F,
    isStratifiedSheaf_of_exists_stratification_top B X _ hPIso hPPull F⟩

end Finite

section Modules

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
  (R : Type r) [CommRing R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]

omit [IsNoetherianRing R] in
/-- **Stacks 095E, modules: the equivalence of (1) and (3).** On a quasi-compact quasi-separated
scheme, a sheaf of modules over a commutative ring is constructible exactly when there is one
finite partition of the whole scheme by constructible locally closed subschemes on each of which
its inverse image is locally constant with finitely generated values. -/
@[stacks 095E "module sheaves, stratification", sga "4 IX 2.4" "(i), modules"]
public theorem isConstructibleModuleSheaf_iff_exists_stratification
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)) :
    IsConstructibleModuleSheaf B X R F ↔
      ∃ s : ConstructibleStratification B X ⊤,
        ∀ i, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
          (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} R)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F) := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} R)}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) G := fun T F G e h =>
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) R e h
  have hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} R)),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T'.obj T'.property) (smallEtalePullObj B q G) := fun T' T q G h =>
    isFiniteTypeLocallyConstant_smallEtaleSheafPullback B R q G h
  exact ⟨exists_stratification_top_of_isStratifiedSheaf B X _ hPIso hPPull F,
    isStratifiedSheaf_of_exists_stratification_top B X _ hPIso hPPull F⟩

end Modules

end AlgebraicGeometry

end
