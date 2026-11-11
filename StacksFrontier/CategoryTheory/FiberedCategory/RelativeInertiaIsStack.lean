module

public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaIsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.StackTransport
import StacksCore.Tactic.StacksAttribute

/-!
# The relative inertia of a 1-morphism of stacks is a stack

Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `p' : 𝒳' ⥤ 𝒞` be stacks and let `F : 𝒳 ⥤ 𝒳'` be a
1-morphism of stacks over `𝒞`. This file proves Stacks 036Y: the relative inertia `I_{𝒳/𝒳'}`
(`CategoryTheory.RelativeInertia F`, with structure functor `π ⋙ p`) and the inertia `I_𝒳`
(`CategoryTheory.AbsoluteInertia p`, with structure functor `CategoryTheory.RelativeInertia.toBase
p`) are stacks, stacks in groupoids if `𝒳` and `𝒳'` are, and stacks in setoids if `𝒳` and `𝒳'`
are.

The absolute case, `CategoryTheory.RelativeInertia.isStack_toBase`, is read off from Stacks 06NS
(`CategoryTheory.RelativeInertia.isStackification_functoriality`) applied to the identity
1-morphism of `p`, which exhibits the stack `p` as its own stackification: the stackification of
the inertia, which 06NS shows to be a stack, is then the inertia of `p` itself.

The relative case is reduced to the absolute one. The relative inertia is, as a category over
`𝒞`, the full subcategory of `I_𝒳` on the pairs `(x, α)` with `F α = 𝟙`. That property is closed
under isomorphism and under strongly cartesian pullback, `F` preserving strongly cartesian
morphisms, and it is local on the base because the presheaf `Mor(F x, F x)` is a sheaf, `𝒳'` being
a stack. A full subcategory of a stack with these properties is a stack (Stacks 04TU), and being a
stack is invariant under equivalence over the base (Stacks 042W). This replaces the 2-fibre product
argument of the source, which identifies `I_{𝒳/𝒳'}` with the 2-fibre product of the diagonal of
`F` with itself (Stacks 034H (1)) and uses that 2-fibre products of stacks are stacks.

## Main results

* `CategoryTheory.RelativeInertia.isStack_π_comp`: the relative inertia of a 1-morphism of stacks
  is a stack.
* `CategoryTheory.RelativeInertia.isStack_of_isStack`,
  `CategoryTheory.RelativeInertia.isStack_and_fiber_isGroupoid_of_isStack`,
  `CategoryTheory.RelativeInertia.isStackInSetoids_of_isStackInSetoids`: Stacks 036Y (1), (2), (3).
-/

@[expose] public section

namespace CategoryTheory

universe vb v v' u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒳' : Type u₃} [Category.{v'} 𝒳']

namespace RelativeInertia

/-! ## The relative inertia as a full subcategory of the inertia -/

variable {F : 𝒳 ⥤ 𝒳'} {p : 𝒳 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {J : GrothendieckTopology 𝒞}

variable (F p) in
/-- The objects `(x, α)` of the inertia `I_𝒳` of `p` whose automorphism `α` is sent to an identity
by `F : 𝒳 ⥤ 𝒳'`: these are the objects of the relative inertia `I_{𝒳/𝒳'}`. -/
def relativeProperty : ObjectProperty (RelativeInertia p) :=
  fun A ↦ F.map A.auto.asIso.hom = 𝟙 (F.obj A.obj)

instance : (relativeProperty F p).IsClosedUnderIsomorphisms where
  of_iso {A B} e hA := by
    have hA : F.map A.auto.asIso.hom = 𝟙 _ := hA
    have : IsIso e.hom.hom := (inferInstance : IsIso ((RelativeInertia.π p).map e.hom))
    have h := congrArg F.map e.hom.comm
    simp only [F.map_comp, hA, Category.id_comp] at h
    exact (cancel_epi (F.map e.hom.hom)).1 (h.trans (Category.comp_id _).symm)

/-- The image under `F` of the automorphism of an object of the inertia of `p` lies over an
identity. -/
lemma isHomLift_map_auto (hF : p.IsFibredOneMorphism p' F) (A : RelativeInertia p) {R : 𝒞}
    (hA : p.obj A.obj = R) : p'.IsHomLift (𝟙 R) (F.map A.auto.asIso.hom) := by
  subst hA
  have h := IsHomLift.map (p := p) A.auto.asIso.hom
  rw [A.cond] at h
  exact hF.map_isHomLift _ _

/-- The objects of the relative inertia are closed under strongly cartesian pullback in the
inertia: `F` sends a strongly cartesian morphism of `𝒳` to a strongly cartesian morphism of
`𝒳'`, along which an automorphism lying over an identity is determined by its composite. -/
lemma closedUnderStronglyCartesian_relativeProperty [p.IsFibered]
    (hF : p.IsFibredOneMorphism p' F) :
    Functor.ClosedUnderStronglyCartesianUpToIso (RelativeInertia.toBase p)
      (relativeProperty F p) := by
  intro V U y x f φ hφ hx
  refine (relativeProperty F p).le_isoClosure _ ?_
  have := hφ.toIsHomLift
  have hφ' : p'.IsStronglyCartesian f (F.map φ.hom) :=
    hF.map_isStronglyCartesian f φ.hom ((isFibredOneMorphism_π p).map_isStronglyCartesian f φ hφ)
  have : p'.IsCartesian f (F.map φ.hom) := inferInstance
  have := isHomLift_map_auto hF y (IsHomLift.domain_eq (RelativeInertia.toBase p) f φ)
  have hx : F.map x.auto.asIso.hom = 𝟙 _ := hx
  have h := congrArg F.map φ.comm
  simp only [F.map_comp, hx, Category.comp_id] at h
  exact (Functor.IsCartesian.map_uniq p' f (F.map φ.hom) (F.map φ.hom) _ h.symm).trans
    (Functor.IsCartesian.map_self p' f _)

/-- The objects of the relative inertia are local in the inertia: if the pullbacks of `(x, α)`
to a covering have `F`-trivial automorphism, then so does `(x, α)`, the presheaf
`Mor(F x, F x)` being a sheaf. -/
lemma locallyClosed_relativeProperty [p.IsFibered] [(RelativeInertia.toBase p).IsFibered]
    (hp' : p'.IsStack J) (hF : p.IsFibredOneMorphism p' F) :
    Functor.LocallyClosedUpToIso (RelativeInertia.toBase p) (relativeProperty F p) J := by
  intro U ι Uᵢ fᵢ hcov x hx
  refine (relativeProperty F p).le_isoClosure _ ?_
  have := hp'.isFibered
  have hxU : p.obj x.1.obj = U := x.2
  have := isHomLift_map_auto hF x.1 hxU
  let X' : p'.Fiber U := ⟨F.obj x.1.obj, (Functor.congr_obj hF.comp_eq x.1.obj).trans hxU⟩
  let m : X' ⟶ X' := ⟨F.map x.1.auto.asIso.hom, inferInstance⟩
  suffices key : m = 𝟙 X' from congrArg Subtype.val key
  refine Functor.eq_of_pullbackFiberHom_locally_eq p' (hp'.isMorSheaf U X' X') hcov
    fun V g hg => ?_
  obtain ⟨W, h, _, ⟨i⟩, rfl⟩ := hg
  rw [Functor.pullbackFiberHom_id]
  refine (Functor.pullbackFiberHom_uniq m _ (𝟙 _) ?_).symm
  let ψ := Functor.IsPreFibered.pullbackMap x.2 (fᵢ i)
  have hψ : p'.IsStronglyCartesian (fᵢ i) (F.map ψ.hom) :=
    hF.map_isStronglyCartesian _ _
      ((isFibredOneMorphism_π p).map_isStronglyCartesian _ ψ inferInstance)
  have hxi : F.map (Functor.IsPreFibered.pullbackObj x.2 (fᵢ i)).auto.asIso.hom = 𝟙 _ := by
    obtain ⟨Y, hY, ⟨e⟩⟩ := hx i
    exact (relativeProperty F p).prop_of_iso e.symm hY
  have hc : F.map ψ.hom ≫ F.map x.1.auto.asIso.hom = F.map ψ.hom := by
    rw [← F.map_comp, ψ.comm, F.map_comp, hxi, Category.id_comp]
  have hk := Functor.IsStronglyCartesian.fac p' (fᵢ i) (F.map ψ.hom) (rfl : h ≫ fᵢ i = h ≫ fᵢ i)
    (Functor.IsPreFibered.pullbackMap X'.2 (h ≫ fᵢ i))
  have key : Functor.IsPreFibered.pullbackMap X'.2 (h ≫ fᵢ i) ≫ F.map x.1.auto.asIso.hom =
      Functor.IsPreFibered.pullbackMap X'.2 (h ≫ fᵢ i) := by
    rw [← hk, Category.assoc, hc]
  exact (Category.id_comp _).trans key.symm

/-- The relative inertia `I_{𝒳/𝒳'}`, with structure functor `π ⋙ p`, is the full subcategory
`relativeProperty F p` of the inertia `I_𝒳` of `p`, as categories over `𝒞`; the two are in fact
isomorphic over `𝒞`. -/
def relativeEquivalence (hF : F ⋙ p' = p) : BasedCategory.Equivalence
    (BasedCategory.ofFunctor
      (Functor.restrict (RelativeInertia.toBase p) (relativeProperty F p)))
    (BasedCategory.ofFunctor (RelativeInertia.π F ⋙ p)) where
  functor :=
    { obj A := ⟨A.obj.obj, A.obj.auto, A.property⟩
      map φ := ⟨φ.hom.hom, φ.hom.comm⟩
      map_id _ := rfl
      map_comp _ _ := rfl
      w := rfl }
  inverse :=
    { obj B := ⟨⟨B.obj, B.auto, struct_map_auto_eq_id p p' hF B⟩, B.cond⟩
      map φ := ObjectProperty.homMk ⟨φ.hom, φ.comm⟩
      map_id _ := rfl
      map_comp _ _ := rfl
      w := rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-! ## Stacks 036Y -/

/-- **The relative inertia of a 1-morphism of stacks is a stack.** If `p : 𝒳 ⥤ 𝒞` and
`p' : 𝒳' ⥤ 𝒞` are stacks over `(𝒞, J)` and `F : 𝒳 ⥤ 𝒳'` is a 1-morphism of stacks, the relative
inertia `I_{𝒳/𝒳'}`, with structure functor `π ⋙ p`, is a stack over `𝒞`. -/
theorem isStack_π_comp (hp : p.IsStack J) (hp' : p'.IsStack J)
    (hF : p.IsFibredOneMorphism p' F) : (RelativeInertia.π F ⋙ p).IsStack J := by
  have := hp.isFibered
  have hI := isStack_toBase hp
  have := hI.isFibered
  exact (relativeEquivalence hF.comp_eq).isStack J
    (Functor.IsStack.fullSubcategory_of_isClosedUnderIsomorphisms _ J hI _
      (closedUnderStronglyCartesian_relativeProperty hF)
      (locallyClosed_relativeProperty hp' hF))

/-- Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `p' : 𝒳' ⥤ 𝒞` be stacks and let `F : 𝒳 ⥤ 𝒳'` be
a 1-morphism of stacks. Then the relative inertia `I_{𝒳/𝒳'}` (structure functor `π ⋙ p`) and the
inertia `I_𝒳` (structure functor `toBase p`) are stacks over `𝒞`. -/
@[stacks 036Y "(1)"]
theorem isStack_of_isStack (hp : p.IsStack J) (hp' : p'.IsStack J)
    (hF : p.IsFibredOneMorphism p' F) :
    (RelativeInertia.π F ⋙ p).IsStack J ∧ (RelativeInertia.toBase p).IsStack J :=
  ⟨isStack_π_comp hp hp' hF, isStack_toBase hp⟩

/-- Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `p' : 𝒳' ⥤ 𝒞` be stacks in groupoids and let
`F : 𝒳 ⥤ 𝒳'` be a 1-morphism of stacks. Then the relative inertia `I_{𝒳/𝒳'}` and the inertia
`I_𝒳` are stacks in groupoids. A stack in groupoids is spelled out as a stack all of whose fibre
categories are groupoids. -/
@[stacks 036Y "(2), a stack in groupoids written out as a stack with groupoid fibres"]
theorem isStack_and_fiber_isGroupoid_of_isStack (hp : p.IsStack J)
    (hgp : ∀ U, IsGroupoid (p.Fiber U)) (hp' : p'.IsStack J)
    (_hgp' : ∀ U, IsGroupoid (p'.Fiber U)) (hF : p.IsFibredOneMorphism p' F) :
    ((RelativeInertia.π F ⋙ p).IsStack J ∧
        ∀ U, IsGroupoid ((RelativeInertia.π F ⋙ p).Fiber U)) ∧
      ((RelativeInertia.toBase p).IsStack J ∧
        ∀ U, IsGroupoid ((RelativeInertia.toBase p).Fiber U)) :=
  ⟨⟨isStack_π_comp hp hp' hF, fun U ↦ fiber_isGroupoid F p U (hgp U)⟩,
    ⟨isStack_toBase hp, fun U ↦ fiber_isGroupoid p p U (hgp U)⟩⟩

/-- Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `p' : 𝒳' ⥤ 𝒞` be stacks in setoids and let
`F : 𝒳 ⥤ 𝒳'` be a 1-morphism of stacks. Then the relative inertia `I_{𝒳/𝒳'}` and the inertia
`I_𝒳` are stacks in setoids. -/
@[stacks 036Y "(3)"]
theorem isStackInSetoids_of_isStackInSetoids (hp : p.IsStackInSetoids J)
    (hp' : p'.IsStackInSetoids J) (hF : p.IsFibredOneMorphism p' F) :
    (RelativeInertia.π F ⋙ p).IsStackInSetoids J ∧
      (RelativeInertia.toBase p).IsStackInSetoids J :=
  ⟨{ isStack := isStack_π_comp hp.isStack hp'.isStack hF
     fiber_isGroupoid U := fiber_isGroupoid F p U (hp.fiber_isGroupoid U)
     fiber_isThin U := fiber_isThin F p U (hp.fiber_isThin U) },
   { isStack := isStack_toBase hp.isStack
     fiber_isGroupoid U := fiber_isGroupoid p p U (hp.fiber_isGroupoid U)
     fiber_isThin U := fiber_isThin p p U (hp.fiber_isThin U) }⟩

end RelativeInertia

end CategoryTheory
