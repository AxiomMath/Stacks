module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CokernelComp
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Kernel
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.PullbackStableLocallyFree

/-!
# Flags of a module with finite locally free graded pieces

Let `M` be a module on a scheme `T`. A *flag of length `m`* of `M`, in the sense used here, is a
decreasing chain of subobjects `M ⊇ K₀ ⊇ K₁ ⊇ ⋯ ⊇ K_{m-1}` such that each quotient `M / K_i` is
finite locally free of rank `i + 1`. Equivalently (by rank additivity), `M ⊇ K₀` has an
invertible quotient and each `K_i / K_{i+1}` is invertible. These are the `T`-points of an
iterated projective bundle (`StacksFrontier.AlgebraicGeometry.FlagTower.Tower`): the first step
`M ↠ M / K₀` is an invertible quotient of `M`, a point of `𝐏(M)`, and the remaining steps are a
flag of `K₀`, a point of the tower over `𝐏(M)` built on the tautological kernel.

Subobjects are used rather than quotient maps so that two flags are *equal*, not merely
isomorphic, when they define the same filtration; this makes "the morphisms into a tower are the
flags" a bijection of types with no further quotient.

## Main definitions

* `Stacks.FlagTower.Flag M m`: flags of length `m` of `M`.
* `Stacks.FlagTower.Flag.cons`: prepend to a flag of `A` the subobject cut out by a mono
  `j : A ⟶ M` with invertible cokernel, giving a flag of `M` of length one more.
* `Stacks.FlagTower.Flag.tail`: the inverse operation, and `Stacks.FlagTower.Flag.consEquiv`.
* `Stacks.FlagTower.Flag.pullback`: the base change of a flag along a morphism of schemes, which
  exists because pullback keeps the inclusion of a subobject with locally free cokernel a
  monomorphism.
* `Stacks.FlagTower.invertibleQuotientClassEquiv`: the isomorphism classes of invertible
  quotients of `M` are the subobjects of `M` with cokernel of rank one, by taking kernels.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.FlagTower

/-! ### Ranks along short exact sequences of cokernels -/

section Rank

variable {T : Scheme.{u}}

/-- The cokernel of the arrow of `Subobject.mk f` is the cokernel of `f`. -/
def cokernelMkArrowIso {A M : T.Modules} (f : A ⟶ M) [Mono f] :
    cokernel (Subobject.mk f).arrow ≅ cokernel f :=
  cokernelIsoOfEq (Subobject.underlyingIso_hom_comp_eq_mk f).symm ≪≫
    cokernelEpiComp (Subobject.underlyingIso f).hom f

/-- Finite local freeness of a given rank of the cokernel of `Subobject.mk f` is that of the
cokernel of `f`. -/
theorem rank_cokernel_mk_iff {A M : T.Modules} (f : A ⟶ M) [Mono f] (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (cokernel (Subobject.mk f).arrow) r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (cokernel f) r :=
  ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (cokernelMkArrowIso f),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (cokernelMkArrowIso f).symm⟩

/-- **The cokernel of a composite of monomorphisms has the summed rank.** For monos
`a : A ⟶ B`, `j : B ⟶ M` the sequence `0 ⟶ coker a ⟶ coker (a ≫ j) ⟶ coker j ⟶ 0` is short
exact, so ranks `r` and `s` of the outer cokernels give rank `r + s` in the middle. -/
theorem rank_cokernel_comp {A B M : T.Modules} (a : A ⟶ B) (j : B ⟶ M) [Mono a] [Mono j]
    (r s : ℕ)
    (ha : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (cokernel a) r)
    (hj : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (cokernel j) s) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel (a ≫ j)) (r + s) :=
  Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _
    (Stacks.Chow.GenuineChern.shortExact_cokernelCompSequence a j) r s ha hj

/-- **The converse rank count**: if `coker (a ≫ j)` has rank `r + s` and `coker j` has rank
`s`, then `coker a` has rank `r`. It is the kernel of a surjection of finite locally free
modules, hence finite locally free, and its rank is the difference. -/
theorem rank_cokernel_of_comp {A B M : T.Modules} (a : A ⟶ B) (j : B ⟶ M) [Mono a] [Mono j]
    (r s : ℕ)
    (haj : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel (a ≫ j)) (r + s))
    (hj : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (cokernel j) s) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (cokernel a) r := by
  have hS := Stacks.Chow.GenuineChern.shortExact_cokernelCompSequence a j
  have h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel (a ≫ j)) :=
    have := haj
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (r + s)
  have h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel j) :=
    have := hj
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ s
  have h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel a) :=
    Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact _ hS
        h₂
        h₃
  have := Stacks.Conormal.isFiniteLocallyFreeOfRank_X₁_of_shortExact _ hS (r + s) s h₁ haj hj
  rwa [Nat.add_sub_cancel] at this

/-- A subobject with finite locally free cokernel is the kernel of its cokernel map: the short
complex `K ⟶ M ⟶ coker K` is short exact. -/
theorem shortExact_arrow_cokernel {M : T.Modules} (S : Subobject M) :
    (ShortComplex.mk S.arrow (cokernel.π S.arrow) (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_cokernel S.arrow }

/-- A module finite locally free of some rank is locally free. -/
theorem isLocallyFree_of_rank {M : T.Modules} {r : ℕ}
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    _root_.SheafOfModules.IsLocallyFree M := by
  obtain ⟨q, hq, -⟩ := h.exists_isFiniteLocallyFreeOfRankData
  exact ⟨q, hq⟩

/-- **Pullback keeps the inclusion of a subobject with locally free cokernel a monomorphism.** -/
theorem mono_pullback_map_arrow {T' : Scheme.{u}} (k : T' ⟶ T) {M : T.Modules}
    (S : Subobject M) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel S.arrow) r) :
    Mono ((Scheme.Modules.pullback k).map S.arrow) :=
  (shortExact_map_pullback_of_isLocallyFree k (shortExact_arrow_cokernel S)
    (isLocallyFree_of_rank h)).mono_f

end Rank

/-! ### Flags -/

variable {T : Scheme.{u}}

/-- **A flag of length `m` of a module `M`**: a decreasing chain of subobjects
`K₀ ⊇ K₁ ⊇ ⋯ ⊇ K_{m-1}` of `M` with `M / K_i` finite locally free of rank `i + 1`. -/
structure Flag (M : T.Modules) (m : ℕ) where
  /-- The subobjects of the flag. -/
  sub : Fin m → Subobject M
  /-- The chain is decreasing. -/
  antitone : Antitone sub
  /-- The `i`-th quotient is finite locally free of rank `i + 1`. -/
  rank : ∀ i : Fin m,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel (sub i).arrow) (i + 1)

namespace Flag

/-- Two flags with the same subobjects are equal. -/
@[ext]
theorem ext {M : T.Modules} {m : ℕ} {F G : Flag M m} (h : F.sub = G.sub) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- The flags of length zero: there is exactly one. -/
instance {M : T.Modules} : Unique (Flag M 0) where
  default := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  uniq _ := Flag.ext (funext fun i => i.elim0)

section Cons

variable {A M : T.Modules} (j : A ⟶ M) [Mono j]
  (hj : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (cokernel j) 1)

/-- The image of a subobject of `A` under a mono `j : A ⟶ M` is `mk (S.arrow ≫ j)`. -/
theorem map_obj_eq_mk (S : Subobject A) : (Subobject.map j).obj S = Subobject.mk (S.arrow ≫ j) := by
  conv_lhs => rw [← Subobject.mk_arrow S]
  exact Subobject.map_mk _ _

/-- The arrow of the image of `S` under `j` is `S.arrow ≫ j`, up to an isomorphism of the
underlying objects. -/
def mapIso (S : Subobject A) : ((Subobject.map j).obj S : T.Modules) ≅ (S : T.Modules) :=
  Subobject.isoOfEq _ _ (map_obj_eq_mk j S) ≪≫ Subobject.underlyingIso (S.arrow ≫ j)

/-- The arrow of the image of `S` under `j` is `S.arrow ≫ j` composed with `mapIso j S`. -/
theorem map_arrow (S : Subobject A) :
    ((Subobject.map j).obj S).arrow = (mapIso j S).hom ≫ S.arrow ≫ j := by
  rw [mapIso, Iso.trans_hom, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk,
    Subobject.isoOfEq_hom, Subobject.ofLE_arrow]

include hj in
/-- The rank of the cokernel of the image of a flag member: one more than in `A`. -/
theorem rank_map {m : ℕ} (F : Flag A m) (i : Fin m) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel ((Subobject.map j).obj (F.sub i)).arrow) (i + 1 + 1) := by
  rw [map_obj_eq_mk, rank_cokernel_mk_iff]
  exact rank_cokernel_comp _ _ _ _ (F.rank i) hj

include hj in
/-- **Prepending the subobject cut out by `j`**: from a flag `(S_i)` of `A` and a mono
`j : A ⟶ M` with invertible cokernel, the flag `j(A) ⊇ j(S₀) ⊇ j(S₁) ⊇ ⋯` of `M`. -/
def cons {m : ℕ} (F : Flag A m) : Flag M (m + 1) where
  sub := Fin.cons (Subobject.mk j) fun i => (Subobject.map j).obj (F.sub i)
  antitone := by
    rw [Fin.antitone_iff_succ_le]
    intro i
    rcases m with _ | m
    · exact i.elim0
    refine Fin.cases ?_ (fun i => ?_) i
    · change (Subobject.map j).obj (F.sub 0) ≤ Subobject.mk j
      rw [map_obj_eq_mk]
      exact Subobject.mk_le_mk_of_comm (F.sub 0).arrow rfl
    · change (Subobject.map j).obj (F.sub i.succ) ≤ (Subobject.map j).obj (F.sub i.castSucc)
      exact (Subobject.map j).monotone (F.antitone (Fin.castSucc_le_succ i))
  rank := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (cokernel (Subobject.mk j).arrow) 1
      exact (rank_cokernel_mk_iff j 1).mpr hj
    · exact rank_map j hj F i

/-- The first member of `cons j hj F` is the subobject `mk j`. -/
@[simp]
theorem cons_sub_zero {m : ℕ} (F : Flag A m) : (cons j hj F).sub 0 = Subobject.mk j :=
  rfl

/-- The `(i + 1)`-th member of `cons j hj F` is the image under `j` of the `i`-th member of `F`.
-/
@[simp]
theorem cons_sub_succ {m : ℕ} (F : Flag A m) (i : Fin m) :
    (cons j hj F).sub i.succ = (Subobject.map j).obj (F.sub i) :=
  rfl

/-- The members of a flag of `M` starting at `mk j` lie below `mk j`. -/
theorem le_mk_of_sub_zero {m : ℕ} (G : Flag M (m + 1)) (hG : G.sub 0 = Subobject.mk j)
    (i : Fin (m + 1)) : G.sub i ≤ Subobject.mk j :=
  hG ▸ G.antitone (Fin.zero_le i)

/-- The subobject of `A` that `j` carries onto a subobject `S ≤ mk j` of `M`. -/
theorem map_pullback_of_le {S : Subobject M} (hS : S ≤ Subobject.mk j) :
    (Subobject.map j).obj ((Subobject.pullback j).obj S) = S := by
  have hT : (Subobject.map j).obj (Subobject.mk (Subobject.ofLEMk S j hS)) = S := by
    rw [Subobject.map_mk]
    exact Subobject.mk_eq_of_comm _ (Iso.refl _) (by simp)
  rw [← hT, Subobject.pullback_map_self]

/-- **Dropping the first member of a flag starting at `mk j`**: the flag of `A` that `j` carries
onto the remaining members. -/
def tail {m : ℕ} (G : Flag M (m + 1)) (hG : G.sub 0 = Subobject.mk j) : Flag A m where
  sub i := (Subobject.pullback j).obj (G.sub i.succ)
  antitone := fun _ _ h => (Subobject.pullback j).monotone (G.antitone (Fin.succ_le_succ_iff.mpr h))
  rank := by
    intro i
    have h1 := G.rank i.succ
    rw [← map_pullback_of_le j (le_mk_of_sub_zero j G hG i.succ), map_obj_eq_mk,
      rank_cokernel_mk_iff] at h1
    exact rank_cokernel_of_comp _ _ _ 1 h1 hj

/-- **Flags of `M` starting at `mk j` are flags of `A`.** -/
def consEquiv (m : ℕ) : Flag A m ≃ { G : Flag M (m + 1) // G.sub 0 = Subobject.mk j } where
  toFun F := ⟨cons j hj F, rfl⟩
  invFun G := tail j hj G.1 G.2
  left_inv F := Flag.ext (funext fun i => Subobject.pullback_map_self j (F.sub i))
  right_inv G := by
    refine Subtype.ext (Flag.ext (funext fun i => ?_))
    refine Fin.cases ?_ (fun i => ?_) i
    · exact G.2.symm
    · exact map_pullback_of_le j (le_mk_of_sub_zero j G.1 G.2 i.succ)

end Cons

section Pullback

variable {T' : Scheme.{u}} (k : T' ⟶ T) {M : T.Modules} {M' : T'.Modules}
  (e : M' ≅ (Scheme.Modules.pullback k).obj M)

set_option synthInstance.maxHeartbeats 400000 in
/-- The cokernel of the base change of a subobject inclusion is the base change of the cokernel. -/
def cokernelPullbackIso (S : Subobject M) :
    cokernel ((Scheme.Modules.pullback k).map S.arrow ≫ e.inv) ≅
      (Scheme.Modules.pullback k).obj (cokernel S.arrow) :=
  cokernelCompIsIso _ _ ≪≫ (PreservesCokernel.iso (Scheme.Modules.pullback k) S.arrow).symm

/-- **The base change of a flag** along `k : T' ⟶ T`, read in a module `M' ≅ k^*M`: the member
`K_i` goes to the image of `k^*K_i ⟶ k^*M ≅ M'`, which is again a subobject because `M / K_i`
is locally free. -/
def pullback {m : ℕ} (F : Flag M m) : Flag M' m where
  sub i := haveI := mono_pullback_map_arrow k (F.sub i) _ (F.rank i)
    Subobject.mk ((Scheme.Modules.pullback k).map (F.sub i).arrow ≫ e.inv)
  antitone a b hab := by
    have := mono_pullback_map_arrow k (F.sub a) _ (F.rank a)
    have := mono_pullback_map_arrow k (F.sub b) _ (F.rank b)
    refine Subobject.mk_le_mk_of_comm
      ((Scheme.Modules.pullback k).map (Subobject.ofLE _ _ (F.antitone hab))) ?_
    rw [← Category.assoc, ← Functor.map_comp, Subobject.ofLE_arrow]
  rank i := by
    have := mono_pullback_map_arrow k (F.sub i) _ (F.rank i)
    rw [rank_cokernel_mk_iff]
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (cokernelPullbackIso k e (F.sub i)).symm
      (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ k _ _ (F.rank i))

end Pullback

end Flag

/-! ### Invertible quotients are subobjects with cokernel of rank one -/

section InvertibleQuotient

variable {M : T.Modules}

/-- An invertible module is finite locally free of rank one (Tag 0B8M). -/
theorem rank_one_of_isInvertible {L : T.Modules}
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible L h

/-- A finite locally free module of rank one is invertible (Tag 0B8M). -/
theorem isInvertible_of_rank_one {L : T.Modules}
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1) :
    AlgebraicGeometry.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    ((Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one T L).mpr h)

/-- **The cokernel of the kernel of an epimorphism is its target**, compatibly with the maps out
of `M`. -/
def kernelSubobjectCokernelIso {L : T.Modules} (q : M ⟶ L) [Epi q] :
    cokernel (kernelSubobject q).arrow ≅ L :=
  cokernelIsoOfEq (kernelSubobject_arrow q).symm ≪≫
    cokernelEpiComp (kernelSubobjectIso q).hom (kernel.ι q) ≪≫
    Stacks.Chow.GenuineChern.cokernelIsoOfShortExact
      (show (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact from
        { exact := ShortComplex.exact_kernel q })

/-- Epimorphisms out of `M` with the same kernel differ by an isomorphism of their targets. -/
theorem exists_iso_of_kernelSubobject_eq {L L' : T.Modules} (q : M ⟶ L) (q' : M ⟶ L')
    [Epi q] [Epi q'] (h : kernelSubobject q = kernelSubobject q') :
    ∃ α : L ≅ L', q ≫ α.hom = q' := by
  have key : ∀ {X Y : T.Modules} (p : M ⟶ X) (p' : M ⟶ Y),
      kernelSubobject p ≤ kernelSubobject p' → kernel.ι p ≫ p' = 0 := fun p p' hle => by
    rw [← kernelSubobject_arrow' p, ← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc,
      kernelSubobject_arrow_comp, comp_zero, comp_zero]
  have w := key q q' h.le
  have w' := key q' q h.ge
  refine ⟨⟨Abelian.epiDesc q q' w, Abelian.epiDesc q' q w', ?_, ?_⟩, Abelian.comp_epiDesc _ _ _⟩
  · rw [← cancel_epi q, Abelian.comp_epiDesc_assoc, Abelian.comp_epiDesc, Category.comp_id]
  · rw [← cancel_epi q', Abelian.comp_epiDesc_assoc, Abelian.comp_epiDesc, Category.comp_id]

/-- **A subobject is the kernel of its cokernel map.** -/
theorem kernelSubobject_cokernel_π (S : Subobject M) : kernelSubobject (cokernel.π S.arrow) = S :=
  le_antisymm
    (Subobject.le_of_comm
      (Abelian.monoLift S.arrow (kernelSubobject (cokernel.π S.arrow)).arrow
        (kernelSubobject_arrow_comp _)) (Abelian.monoLift_comp _ _ _))
    (le_kernelSubobject _ _ (cokernel.condition _))

/-- The kernel of an invertible quotient, as a subobject with cokernel of rank one. -/
def InvertibleQuotient.kernel (Q : Stacks.Divisors.InvertibleQuotient T M) :
    { S : Subobject M //
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (cokernel S.arrow) 1 } :=
  haveI := Q.epi
  ⟨kernelSubobject Q.q,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (kernelSubobjectCokernelIso Q.q).symm (rank_one_of_isInvertible Q.invertible)⟩

/-- **The isomorphism classes of invertible quotients of `M` are the subobjects of `M` whose
cokernel is finite locally free of rank one**, a quotient going to its kernel. -/
def invertibleQuotientClassEquiv (M : T.Modules) :
    Stacks.Divisors.InvertibleQuotientClass T M ≃
      { S : Subobject M //
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (cokernel S.arrow) 1 } :=
  Equiv.ofBijective
    (Quotient.lift InvertibleQuotient.kernel (by
      rintro Q R ⟨α, hα⟩
      have := Q.epi
      exact Subtype.ext (by
        change kernelSubobject Q.q = kernelSubobject R.q
        rw [← hα, kernelSubobject_comp_mono])))
    ⟨by
      rintro ⟨Q⟩ ⟨R⟩ h
      have := Q.epi
      have := R.epi
      obtain ⟨α, hα⟩ := exists_iso_of_kernelSubobject_eq Q.q R.q (congrArg Subtype.val h)
      exact Quotient.sound ⟨α, hα⟩,
    by
      rintro ⟨S, hS⟩
      exact ⟨Quotient.mk _ ⟨cokernel S.arrow, isInvertible_of_rank_one hS, cokernel.π _,
        inferInstance⟩, Subtype.ext (kernelSubobject_cokernel_π S)⟩⟩

/-- `invertibleQuotientClassEquiv M` sends the class of an invertible quotient to its kernel. -/
@[simp]
theorem invertibleQuotientClassEquiv_mk (Q : Stacks.Divisors.InvertibleQuotient T M) :
    invertibleQuotientClassEquiv M
        (Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid T M) Q) =
      InvertibleQuotient.kernel Q :=
  rfl

end InvertibleQuotient

end Stacks.FlagTower

end
